import OAI.Geometry.HarmonicGrowth.ControlWords

namespace OAI

noncomputable section


namespace HarmonicCounterexample.LinearODE
open scoped BigOperators Matrix.Norms.Frobenius

lemma finite_positive_thresholds {β : Type*} [Fintype β] [Nonempty β]
    (t ρ C : β → ℝ) (hρ : ∀ b,0 < ρ b) :
    ∃ T R H : ℝ,1 ≤ T ∧ 0 < R ∧ 1 ≤ H ∧
      (∀ b,t b ≤ T) ∧ (∀ b,R ≤ ρ b) ∧ (∀ b,C b ≤ H) := by
  classical
  obtain ⟨T,hT⟩ := Finite.exists_le t
  obtain ⟨H,hH⟩ := Finite.exists_le C
  refine ⟨max 1 T,Finset.univ.inf' Finset.univ_nonempty ρ,max 1 H,
    le_max_left _ _,?_,le_max_left _ _,fun b => (hT b).trans (le_max_right _ _),
    fun b => Finset.inf'_le ρ (Finset.mem_univ b),fun b => (hH b).trans (le_max_right _ _)⟩
  exact (Finset.lt_inf'_iff _).2 (fun b _ => hρ b)

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.FiniteControl.SmoothWord
open HarmonicCounterexample.LinearODE
open scoped Matrix.Norms.Frobenius
variable {β : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)]

lemma exp_apply (X : MatrixProduct ι) (b : β) :
    (NormedSpace.exp X) b=NormedSpace.exp (X b) := by
  exact NormedSpace.map_exp (Pi.evalAlgHom ℝ (fun b => Matrix (ι b) (ι b) ℝ) b)
    (continuous_apply b) X

lemma leftWord_apply (X : ℕ → MatrixProduct ι) (n : ℕ) (b : β) :
    leftWord X n b=leftWord (fun j => X j b) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (NormedSpace.exp (X n)) b*leftWord X n b=_
    rw [exp_apply,ih]
    rfl

/-- The actual product packet has exactly the actual block packet as each
factor; no norm or ODE product convention is changed in the assembly. -/
lemma actual_packet_apply {n : ℕ} (a : Fin n → ℝ) (X : Fin n → MatrixProduct ι) (b : β) :
    (flow (fun t => ContinuousLinearMap.mul ℝ (MatrixProduct ι)
      (unitPacketCoefficient a X t)) 1 1) b=
    flow (fun t => ContinuousLinearMap.mul ℝ (Matrix (ι b) (ι b) ℝ)
      (unitPacketCoefficient a (fun j => X j b) t)) 1 1 := by
  rw [actual_packet_endpoint,actual_packet_endpoint,leftWord_apply]
  congr 1
  funext j
  by_cases hj : j < n
  · simp only [extendWord,dite_eq_left hj,Pi.smul_apply]
  · simp only [extendWord,dite_eq_right hj,Pi.zero_apply]

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {ξ H κ : Type*} [Fintype ξ] [Nonempty ξ]
  {E : ξ → Type*} {ι : ξ → Type*} {n : ℕ} [NeZero n]
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [Fintype κ]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (H →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedSpace

/-- All retained blocks are controlled simultaneously, using one parameter ball
and thresholds chosen before ANY incoming histories. Both value and outgoing
slope below are the actual center-regular physical solutions. -/
theorem compact_simultaneous_physical_C1 (basis : ∀ b,OrthonormalBasis (ι b) ℝ (E b))
    (hbasis : OrthonormalBasis κ ℝ H) {K : Set H} (hK : IsCompact K)
    (r p₀ γ M : ℝ) (B β θ : ξ → ℝ) (D : ∀ b,Fin n → E b →L[ℝ] E b)
    (hD : ∀ b j v,inner ℝ v (D b j v) ≤ 0)
    (hBD : ∀ b j v,-(B b*‖v‖^2) ≤ inner ℝ v (D b j v))
    (hM : 0 ≤ M) (hB : ∀ b,0 ≤ B b) (hθ : ∀ b,0 < θ b) (hγ : 0 < γ)
    (hden : ∀ b,p₀+2*θ b ≠ 0) (hroot : ∀ b,β b*B b-p₀*θ b-θ b^2=0)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ ρ C : ℝ,1 ≤ T₀ ∧ 0 < ρ ∧ 1 ≤ C ∧ ∀ T ≥ T₀,
      ∀ (history : ∀ b,ℝ → E b →L[ℝ] E b) (α drift : ℝ → ℝ)
        (MH : ξ → ℝ) (Mb : ℝ) (l : ξ → ℝ) (B₀ a δ ε : ℝ) (S : Set H),
      IsOpen S → IsPreconnected S → S ⊆ K →
      (∀ b,ContDiff ℝ ∞ (history b)) → ContDiff ℝ ∞ α → Continuous drift →
      (∀ b,0 ≤ MH b) → 0 ≤ Mb → (∀ t,|α t| ≤ M) → (∀ t,0 ≤ α t) →
      (∀ t,|drift t| ≤ Mb) → (∀ b t,‖history b t‖ ≤ MH b) →
      (∀ b t v,0 ≤ inner ℝ v (history b t v)) →
      (∀ b,∀ t ∈ Icc a (a+T),history b t=α t • (B b • (1:E b →L[ℝ] E b))) →
      (∀ b,0 < l b) → (∀ b,∀ t ≤ 0,∀ v,history b t v=(l b*(l b+B₀)) • v) →
      (∀ t ≤ 0,drift t=B₀) → 0 ≤ a → 0 ≤ δ → 0 ≤ ε →
      (∀ b,∀ t ∈ Icc a (a+T),|α t-β b| ≤ δ) →
      (∀ t ∈ Icc a (a+T),|drift t-p₀| ≤ δ) →
      (∀ t ∈ Icc a (a+T),γ ≤ drift t) → δ+T⁻¹+ε ≤ ρ →
      (∀ b,‖orthogonalMatrix (basis b) (slope (history b) drift (l b) a)-θ b • (1:Matrix (ι b) (ι b) ℝ)‖ ≤ ε) →
      let A := fun b x => insertWord (history b) α r (B b • (1:E b →L[ℝ] E b)) (D b) (fun j => amps j x) a T
      let v := fun b t => scalarBaseline (fun s => α (a+s)*B b) (fun s => drift (a+s)) (θ b) (max 0 (t-a))
      let W := fun x b => orthogonalMatrix (basis b) (flow (fun t => ContinuousLinearMap.mul ℝ (E b →L[ℝ] E b)
        (unitPacketCoefficient (fun j => amps j x) (fun j => bergerSlowGenerator r (B b) (β b) p₀ (θ b) 1 (D b j)) t)) 1 1)
      let Y := fun x b => orthogonalMatrix (basis b) (Real.exp (-(∫ t in a..a+T,v b t)) •
        (operatorValue (A b x) drift (l b) (a+T)*Ring.inverse (operatorValue (A b x) drift (l b) a)))
      let Q := fun x b => orthogonalMatrix (basis b) (slope (A b x) drift (l b) (a+T))-θ b • (1:Matrix (ι b) (ι b) ℝ)
      ∀ x ∈ S,DifferentiableAt ℝ Y x ∧ DifferentiableAt ℝ Q x ∧
        max (max ‖Y x-W x‖ ‖fderiv ℝ Y x-fderiv ℝ W x‖)
          (max ‖Q x‖ ‖fderiv ℝ Q x‖) ≤ C*(δ+T⁻¹+ε) := by
  classical
  choose ts rs cs hts hrs hcs works using fun b => compact_inserted_matrix_C1
    (basis b) hbasis hK r (B b) (β b) p₀ (θ b) γ M (D b) (hD b) (hBD b)
    hM (hB b) (hθ b) hγ (hden b) (hroot b) amps amps' ha hc hd
  obtain ⟨T₀,ρ,C,hT₀,hρ,hC,ht,hρs,hCs⟩ := finite_positive_thresholds ts rs cs hrs
  refine ⟨T₀,ρ,C,hT₀,hρ,hC,?_⟩
  intro T hT history α drift MH Mb l B₀ a δ ε S hS hSc hSK hh hα hb hMH hMb hnα hαpos hnb
    hnH hHpos hround hl hcenter hbcenter ha₀ hδ hε hαclose hbclose hγb hsmall hin
  dsimp only
  intro x hx
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT₀.trans hT)
  have herr : 0 ≤ δ+T⁻¹+ε := by positivity
  have hprod : 0 ≤ C*(δ+T⁻¹+ε) := mul_nonneg (by linarith) herr
  have hlocal (b : ξ) := works b T ((ht b).trans hT) (history b) α drift (MH b) Mb (l b) B₀ a δ ε S
    hS hSc hSK (hh b) hα hb (hMH b) hMb hnα hαpos hnb (hnH b) (hHpos b) (hround b)
    (hl b) (hcenter b) hbcenter ha₀ hδ hε (hαclose b) hbclose hγb (hsmall.trans (hρs b)) (hin b) x hx
  have hm (b : ξ) : cs b*(δ+T⁻¹+ε) ≤ C*(δ+T⁻¹+ε) := mul_le_mul_of_nonneg_right (hCs b) herr
  have hv := finite_C1_error hprod (fun b => (hlocal b).1)
    (fun b => (orthogonalMatrix (basis b)).differentiableAt.comp x
      (actual_packet_differentiableAt amps
        (fun j => bergerSlowGenerator r (B b) (β b) p₀ (θ b) 1 (D b j))
        (fun j => (ha x (hSK hx) j).differentiableAt)))
    (fun b => ((le_max_left _ _).trans (hlocal b).2.2).trans (hm b))
  have hq := finite_C1_norm hprod (fun b => (hlocal b).2.1)
    (fun b => ((le_max_right _ _).trans (hlocal b).2.2).trans (hm b))
  exact ⟨hv.1,hq.1,max_le hv.2 hq.2⟩

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set
open scoped ContDiff BigOperators Matrix.Norms.Frobenius

/-- Restart of an actual scalar second-order equation on a diagonal leg. -/
theorem scalar_restart_on {A b f g : ℝ → ℝ} {c d MA Mb : ℝ}
    (hA : Continuous A) (hb : Continuous b) (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnA : ∀ t,|A t| ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (hfc : ContinuousOn f (Icc c d)) (hgc : ContinuousOn g (Icc c d))
    (hf : ∀ t ∈ Ico c d,HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Ico c d,HasDerivAt g (A t*f t-b t*g t) t) :
    ∀ t ∈ Icc c d,f t=
      scalarU (fun s => A (c+s)) (fun s => b (c+s)) (t-c)*f c+
      scalarV (fun s => A (c+s)) (fun s => b (c+s)) (t-c)*g c := by
  let Ac := fun s => A (c+s)
  let bc := fun s => b (c+s)
  have hAc : Continuous Ac := hA.comp (continuous_const.add continuous_id)
  have hbc : Continuous bc := hb.comp (continuous_const.add continuous_id)
  have hnAc : ∀ s,|Ac s| ≤ MA := fun s => hnA _
  have hnbc : ∀ s,|bc s| ≤ Mb := fun s => hnb _
  let F := fun t => (f t,g t)
  let G := fun t => scalarPhase Ac bc (f c) (g c) (t-c)
  let C := block (fun t => ContinuousLinearMap.mul ℝ ℝ (A t)) b
  have hCb : ∀ t,‖C t‖ ≤ 1+MA+Mb := block_bound hMA hMb
    (fun t => (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℝ _).trans (by simpa using hnA t)) hnb
  have hdG (t : ℝ) : HasDerivAt G (C t (G t)) t := by
    have hct : c+(t-c)=t := by ring
    have hh := (scalarPhase_deriv hAc hbc hMA hMb hnAc hnbc (f c) (g c) (t-c)).scomp t
      ((hasDerivAt_id t).sub_const c)
    simpa only [Function.comp_def,id_eq,one_smul,Ac,bc,add_sub_cancel_left,
      G,C,block_apply,ContinuousLinearMap.mul_apply',hct,smul_eq_mul] using hh
  have he := solution_unique_on_Icc (show 0 ≤ 1+MA+Mb by positivity)
    (fun t _ => hCb t) (hfc.prodMk hgc)
    ((continuous_iff_continuousAt.2 (fun t => (hdG t).continuousAt)).continuousOn)
    (fun t ht => by simpa only [F,C,block_apply,ContinuousLinearMap.mul_apply',smul_eq_mul] using (hf t ht).prodMk (hg t ht))
    (fun t _ => hdG t) (by simp only [G,sub_self,scalarPhase_init])
  intro t ht
  have ht' := congrArg Prod.fst (he ht)
  change f t=(scalarPhase Ac bc (f c) (g c) (t-c)).1 at ht'
  rw [scalarPhase_linear hAc hbc hMA hMb hnAc hnbc] at ht'
  simpa only [mul_comm] using ht'

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixEntry (i j : ι) : Matrix ι ι ℝ →L[ℝ] ℝ :=
  ((LinearMap.proj j : (ι → ℝ) →ₗ[ℝ] ℝ).comp (LinearMap.proj i)).toContinuousLinearMap

omit [DecidableEq ι] in
@[simp] lemma matrixEntry_apply (i j : ι) (X : Matrix ι ι ℝ) : matrixEntry i j X=X i j := rfl

/-- Actual entrywise diagonal propagation, retaining both incoming value and
velocity. No incoming stable eigenspace is imposed. -/
theorem matrix_diagonal_restart {lam : ι → ℝ → ℝ} {b : ℝ → ℝ}
    {F G : ℝ → Matrix ι ι ℝ} {c d Mb : ℝ} (MA : ι → ℝ)
    (hlam : ∀ i,Continuous (lam i)) (hb : Continuous b)
    (hMA : ∀ i,0 ≤ MA i) (hMb : 0 ≤ Mb)
    (hnlam : ∀ i t,|lam i t| ≤ MA i) (hnb : ∀ t,|b t| ≤ Mb)
    (hF : ContinuousOn F (Icc c d)) (hG : ContinuousOn G (Icc c d))
    (hdF : ∀ t ∈ Ico c d,HasDerivAt F (G t) t)
    (hdG : ∀ t ∈ Ico c d,HasDerivAt G
      (Matrix.diagonal (fun i => lam i t)*F t-b t • G t) t) :
    ∀ t ∈ Icc c d,F t=
      Matrix.diagonal (fun i => scalarU (fun s => lam i (c+s)) (fun s => b (c+s)) (t-c))*F c+
      Matrix.diagonal (fun i => scalarV (fun s => lam i (c+s)) (fun s => b (c+s)) (t-c))*G c := by
  intro t ht
  ext i j
  have hf (s : ℝ) (hs : s ∈ Ico c d) : HasDerivAt (fun u => F u i j) (G s i j) s :=
    (matrixEntry i j).hasFDerivAt.comp_hasDerivAt s (hdF s hs)
  have hg (s : ℝ) (hs : s ∈ Ico c d) : HasDerivAt (fun u => G u i j)
      (lam i s*F s i j-b s*G s i j) s := by
    have hh := (matrixEntry i j).hasFDerivAt.comp_hasDerivAt s (hdG s hs)
    change HasDerivAt (fun u => G u i j)
      ((Matrix.diagonal (fun i => lam i s)*F s-b s • G s) i j) s at hh
    simpa only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.smul_apply,
      smul_eq_mul] using hh
  have he := scalar_restart_on (hlam i) hb (hMA i) hMb (hnlam i) hnb
    ((matrixEntry i j).continuous.comp_continuousOn hF)
    ((matrixEntry i j).continuous.comp_continuousOn hG) hf hg t ht
  change F t i j=scalarU (fun s => lam i (c+s)) (fun s => b (c+s)) (t-c)*F c i j+
    scalarV (fun s => lam i (c+s)) (fun s => b (c+s)) (t-c)*G c i j at he
  simpa only [Matrix.add_apply,Matrix.diagonal_mul] using he

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

/-- The complete prescribed diagonal leg for the actual center-regular value
fundamental matrix, not for a model first-order propagator. -/
theorem actual_diagonal_restart (basis : OrthonormalBasis ι ℝ E)
    {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ} {lam : ι → ℝ → ℝ}
    {MA Mb c d : ℝ} (N : ι → ℝ) (l : ℝ)
    (hA : Continuous A) (hb : Continuous b) (hlam : ∀ i,Continuous (lam i))
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb) (hN : ∀ i,0 ≤ N i)
    (hnA : ∀ t,‖A t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb) (hnlam : ∀ i t,|lam i t| ≤ N i)
    (hdiag : ∀ t ∈ Ico c d,orthogonalMatrix basis (A t)=Matrix.diagonal (fun i => lam i t)) :
    ∀ t ∈ Icc c d,orthogonalMatrix basis (operatorValue A b l t)=
      Matrix.diagonal (fun i => scalarU (fun s => lam i (c+s)) (fun s => b (c+s)) (t-c))*
        orthogonalMatrix basis (operatorValue A b l c)+
      Matrix.diagonal (fun i => scalarV (fun s => lam i (c+s)) (fun s => b (c+s)) (t-c))*
        orthogonalMatrix basis (operatorVelocity A b l c) := by
  have hf (t : ℝ) := orthogonalMatrix_hasDerivAt basis (operatorValue_deriv hA hb hMA hMb hnA hnb l t)
  have hg (t : ℝ) := orthogonalMatrix_hasDerivAt basis (operatorVelocity_deriv hA hb hMA hMb hnA hnb l t)
  apply matrix_diagonal_restart N hlam hb hN hMb hnlam hnb
    ((continuous_iff_continuousAt.2 (fun t => (hf t).continuousAt)).continuousOn)
    ((continuous_iff_continuousAt.2 (fun t => (hg t).continuousAt)).continuousOn)
    (fun t _ => hf t)
  intro t ht
  simpa only [map_sub,map_smul,orthogonalMatrix_mul,hdiag t ht] using hg t

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open scoped Matrix.Norms.Frobenius BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup ((ι → ℝ) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((ι → ℝ) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

/-- The fixed Frobenius-coordinate norm cost of the diagonal embedding. -/
def diagonalL : (ι → ℝ) →L[ℝ] Matrix ι ι ℝ :=
  (Matrix.diagonalLinearMap ι ℝ ℝ).toContinuousLinearMap

@[simp] lemma diagonalL_apply (v : ι → ℝ) : diagonalL v=Matrix.diagonal v := rfl

/-- Exact normalization of a positive scalar diagonal leg, with a bound
independent of its length and anisotropy. -/
theorem diagonal_leg_normalizer (u v : ι → ℝ) {θ : ℝ}
    (hu : ∀ i,1 ≤ u i) (hv : ∀ i,0 ≤ v i) (hθ : 0 < θ) :
    ∃ D : (Matrix ι ι ℝ)ˣ,
      (D:Matrix ι ι ℝ)=Matrix.diagonal u+θ • Matrix.diagonal v ∧
      (∀ i,0 < (D:Matrix ι ι ℝ) i i) ∧
      ‖(↑D⁻¹:Matrix ι ι ℝ)*Matrix.diagonal v‖ ≤ ‖diagonalL (ι:=ι)‖*θ⁻¹ := by
  classical
  let d := fun i => u i+θ*v i
  have hd (i : ι) : 0 < d i := by
    have := hu i
    have := mul_nonneg hθ.le (hv i)
    dsimp [d]
    linarith
  let D : (Matrix ι ι ℝ)ˣ :=
    { val := Matrix.diagonal d
      inv := Matrix.diagonal (fun i => (d i)⁻¹)
      val_inv := by
        rw [Matrix.diagonal_mul_diagonal]
        simp only [mul_inv_cancel₀ (hd _).ne']
        exact Matrix.diagonal_one
      inv_val := by
        rw [Matrix.diagonal_mul_diagonal]
        simp only [inv_mul_cancel₀ (hd _).ne']
        exact Matrix.diagonal_one }
  refine ⟨D,?_,?_,?_⟩
  · change Matrix.diagonal d=_
    simp only [d,← Matrix.diagonal_smul,← Matrix.diagonal_add]
    rfl
  · intro i
    simpa only [D,Units.val_mk,Matrix.diagonal_apply_eq] using hd i
  · let k := fun i => v i/d i
    have hkn : ∀ i,|k i| ≤ θ⁻¹ := by
      intro i
      have hk0 : 0 ≤ k i := div_nonneg (hv i) (hd i).le
      rw [abs_of_nonneg hk0]
      apply (div_le_iff₀ (hd i)).2
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ hθ).2
      dsimp [d]
      have := hu i
      nlinarith
    have hk : ‖k‖ ≤ θ⁻¹ := (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hθ.le)).2 hkn
    have he : (↑D⁻¹:Matrix ι ι ℝ)*Matrix.diagonal v=diagonalL k := by
      change Matrix.diagonal (fun i => (d i)⁻¹)*Matrix.diagonal v=Matrix.diagonal k
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      change (d i)⁻¹*v i=v i/d i
      rw [div_eq_mul_inv,mul_comm]
    rw [he]
    exact ((diagonalL (ι:=ι)).le_opNorm k).trans
      (mul_le_mul_of_nonneg_left hk (norm_nonneg _))

/-- The normalizer belongs to the ACTUAL scalar propagation columns, not
freely chosen diagonal data. -/
theorem actual_diagonal_normalizer {A : ι → ℝ → ℝ} {p : ℝ → ℝ}
    (hA : ∀ i,Continuous (A i)) (hp : Continuous p)
    (MA : ι → ℝ) {Mp t θ : ℝ} (hMA : ∀ i,0 ≤ MA i) (hMp : 0 ≤ Mp)
    (hAn : ∀ i s,|A i s| ≤ MA i) (hpn : ∀ s,|p s| ≤ Mp)
    (hAp : ∀ i s,0 ≤ s → 0 ≤ A i s) (ht : 0 ≤ t) (hθ : 0 < θ) :
    ∃ D : (Matrix ι ι ℝ)ˣ,
      (D:Matrix ι ι ℝ)=Matrix.diagonal (fun i => scalarU (A i) p t)+
        θ • Matrix.diagonal (fun i => scalarV (A i) p t) ∧
      (∀ i,0 < (D:Matrix ι ι ℝ) i i) ∧
      ‖(↑D⁻¹:Matrix ι ι ℝ)*Matrix.diagonal (fun i => scalarV (A i) p t)‖ ≤
        ‖diagonalL (ι:=ι)‖*θ⁻¹ := by
  apply diagonal_leg_normalizer _ _ (fun i => ?_) (fun i => ?_) hθ
  · exact (actual_scalar_leg_nonnegative (hA i) hp (hMA i) hMp (hAn i) hpn (hAp i) ht).1
  · exact (actual_scalar_leg_nonnegative (hA i) hp (hMA i) hMp (hAn i) hpn (hAp i) ht).2

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl HarmonicCounterexample.FiniteControl.SmoothWord
open HarmonicCounterexample.FiniteControl.Frobenius HarmonicCounterexample.Transmission
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace

/-- Fixed finite angular and radial constants. -/
structure PulseSystem (E : ξ → Type*) (ι : ξ → Type*) (κ : Type*)
    [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
    [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] where
  basis : ∀ b,OrthonormalBasis (ι b) ℝ (E b)
  r : ℝ
  p₀ : ℝ
  γ : ℝ
  M : ℝ
  B : ξ → ℝ
  β : ξ → ℝ
  θ : ξ → ℝ
  D : ∀ b,κ → E b →L[ℝ] E b
  hD : ∀ b j v,inner ℝ v (D b j v) ≤ 0
  hBD : ∀ b j v,-(B b*‖v‖^2) ≤ inner ℝ v (D b j v)
  hM : 0 ≤ M
  hB : ∀ b,0 ≤ B b
  hθ : ∀ b,0 < θ b
  hγ : 0 < γ
  hden : ∀ b,p₀+2*θ b ≠ 0
  hroot : ∀ b,β b*B b-p₀*θ b-θ b^2=0

variable (S : PulseSystem E ι κ)

def PulseSystem.generator (j : κ) : MatrixProduct ι := fun b =>
  orthogonalMatrix (S.basis b) (bergerSlowGenerator S.r (S.B b) (S.β b) S.p₀ (S.θ b) 1 (S.D b j))

/-- Raw center-regular history plus the quantitative hypotheses used on the
current pulse. This structure contains no transmission conclusion. -/
structure PulseHistory where
  history : ∀ b,ℝ → E b →L[ℝ] E b
  α : ℝ → ℝ
  drift : ℝ → ℝ
  MH : ξ → ℝ
  Mb : ℝ
  l : ξ → ℝ
  B₀ : ℝ
  a : ℝ
  T : ℝ
  δ : ℝ
  ε : ℝ
  smooth : ∀ b,ContDiff ℝ ∞ (history b)
  αsmooth : ContDiff ℝ ∞ α
  driftContinuous : Continuous drift
  MHnonneg : ∀ b,0 ≤ MH b
  Mbnonneg : 0 ≤ Mb
  αbound : ∀ t,|α t| ≤ S.M
  αnonneg : ∀ t,0 ≤ α t
  driftBound : ∀ t,|drift t| ≤ Mb
  bound : ∀ b t,‖history b t‖ ≤ MH b
  nonneg : ∀ b t v,0 ≤ inner ℝ v (history b t v)
  round : ∀ b,∀ t ∈ Icc a (a+T),history b t=α t • (S.B b • (1:E b →L[ℝ] E b))
  lpos : ∀ b,0 < l b
  center : ∀ b,∀ t ≤ 0,∀ v,history b t v=(l b*(l b+B₀)) • v
  driftCenter : ∀ t ≤ 0,drift t=B₀
  apos : 0 ≤ a
  δnonneg : 0 ≤ δ
  εnonneg : 0 ≤ ε
  αclose : ∀ b,∀ t ∈ Icc a (a+T),|α t-S.β b| ≤ δ
  driftClose : ∀ t ∈ Icc a (a+T),|drift t-S.p₀| ≤ δ
  driftLower : ∀ t ∈ Icc a (a+T),S.γ ≤ drift t
  incoming : ∀ b,‖orthogonalMatrix (S.basis b) (slope (history b) drift (l b) a)-S.θ b • (1:Matrix (ι b) (ι b) ℝ)‖ ≤ ε

/-- Fixed chronological smooth control data and a nonempty compact parameter
ball. Slot count is positive; a globally zero family is not substituted. -/
structure PhysicalWord (κ : Type*) where
  d : ℕ
  n : ℕ
  n_ne : n ≠ 0
  slot : Fin n → κ
  amps : Fin n → EuclideanSpace ℝ (Fin d) → ℝ
  smooth : ∀ j,ContDiff ℝ ∞ (amps j)
  radius : ℝ
  radius_pos : 0 < radius

namespace PhysicalWord
variable (w : PhysicalWord κ) (H : PulseHistory S)
abbrev Parameter := EuclideanSpace ℝ (Fin w.d)
def ball : Set w.Parameter := Metric.closedBall 0 w.radius

def coefficient (b : ξ) (x : w.Parameter) : ℝ → E b →L[ℝ] E b :=
  insertWord (H.history b) H.α S.r (S.B b • (1:E b →L[ℝ] E b))
    (fun j => S.D b (w.slot j)) (fun j => w.amps j x) H.a H.T

def baseline (b : ξ) (t : ℝ) : ℝ :=
  scalarBaseline (fun s => H.α (H.a+s)*S.B b) (fun s => H.drift (H.a+s)) (S.θ b) (max 0 (t-H.a))

def value (x : w.Parameter) : MatrixProduct ι := fun b =>
  orthogonalMatrix (S.basis b) (Real.exp (-(∫ t in H.a..H.a+H.T,baseline S H b t)) •
    (operatorValue (w.coefficient S H b x) H.drift (H.l b) (H.a+H.T)*
      Ring.inverse (operatorValue (w.coefficient S H b x) H.drift (H.l b) H.a)))

def defect (x : w.Parameter) : MatrixProduct ι := fun b =>
  orthogonalMatrix (S.basis b) (slope (w.coefficient S H b x) H.drift (H.l b) (H.a+H.T))-
    S.θ b • (1:Matrix (ι b) (ι b) ℝ)

def ideal (x : w.Parameter) : MatrixProduct ι :=
  flow (fun t => ContinuousLinearMap.mul ℝ (MatrixProduct ι)
    (unitPacketCoefficient (fun j => w.amps j x) (S.generator ∘ w.slot) t)) 1 1

end PhysicalWord
end HarmonicCounterexample.LinearODE

end

end OAI
