import Mathlib
import OAI.Geometry.BallPacking.Layers.LayerAreaForm

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section

open scoped ContDiff Topology BigOperators
open Set Function

theorem exists_final_surface_layer_packing {m N : ℕ}
    {δ α β : ℝ} (hδ : 0<δ) (hsmall : δ<1/2) (hαβ : α<β)
    {A B : Plane → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hB : ContDiffOn ℝ ∞ B (Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ)))
    (hbase : ∀ q∈Ioo α β ×ˢ Ioo (1/2-δ) (1/2+δ),0<fderiv ℝ B q (1,0)-fderiv ℝ A q (0,1))
    (J : (Fin m → ℝ) → ℝ) (R : PlanePhase (Fin m) → ℝ) (H : Fin N → (Fin m → ℝ) → ℝ)
    (hJ : ContDiff ℝ ∞ J) (hR : ContDiff ℝ ∞ R) (hH : ∀ i,ContDiff ℝ ∞ (H i))
    {V : Set (Fin m → ℝ)} (hV : IsOpen (planeMoments ⁻¹' V)) (hHp : ∀ i p,p∈V → 0≤H i p)
    (r r' : Fin N → ℝ) (hr' : ∀ i,0≤r' i) (hrr : ∀ i,r' i<r i)
    (hsimplex : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → (∑ j,p j)≤r' i → p∈V)
    (hheight : ∀ i,∀ p : Fin m → ℝ,(∀ j,0≤p j) → p∈V → r i - (∑ j,p j) ≤ H i p) :
    ∃ lo hi : Fin (N+1) → ℝ, ∃ ρ : Fin (N+1) → ℝ → ℝ,
      (∀ i,α<lo i ∧ lo i<hi i ∧ hi i<β) ∧
      (∀ i j,i<j → hi i<lo j) ∧
      (∀ i,ContDiff ℝ ∞ (ρ i) ∧ Monotone (ρ i)) ∧
      (∀ i s,0≤ρ i s ∧ ρ i s≤1 ∧ 0≤deriv (ρ i) s) ∧
      (∀ i, ∃ ε : ℝ, 0 < ε ∧ (∀ s, s ≤ lo i + ε → ρ i s = 0) ∧ (∀ s, hi i - ε ≤ s → ρ i s = 1)) ∧
      ∃ (U : Fin N → Set (Ambient (m+1))) (φ : Fin N → Ambient (m+1) → Plane × PlanePhase (Fin m)),
        (∀ i,IsOpen (U i)) ∧ (∀ i,closedBall (m+1) (r' i)⊆U i) ∧
        (∀ i,ContDiffOn ℝ ∞ (φ i) (U i)) ∧
        (∀ i,Topology.IsEmbedding (fun z : U i => φ i z)) ∧
        (∀ i,∀ z∈U i,φ i z∈(Ioo (lo i.castSucc) (hi i.castSucc) ×ˢ Ioo (1/2-δ) (1/2+δ)) ×ˢ
          (planeMoments ⁻¹' V)) ∧
        (∀ i,∀ z∈U i,∀ v u,
          horizontalCoupling phaseArea (baseCoefficient A)
            (weightedSecondCoefficient B (fun q => positiveCircleClock δ (circleTurn q.2))
              (surfaceFinalLayer (J ∘ planeMoments) (fun j => H j ∘ planeMoments) R
                (fun j => ρ j.castSucc) (ρ (Fin.last N))))
            (φ i z) (fderiv ℝ (φ i) z v) (fderiv ℝ (φ i) z u)=standardForm v u) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+1) (r' i))
          (φ j '' closedBall (m+1) (r' j))) := by
  classical
  obtain ⟨lo,hi,ρ,hbd,hord,hsm,hpos,hcol,hiso⟩ := exists_surface_layer_clocks N hαβ
  let F : Fin N → (Fin m → ℝ) → ℝ := fun i p => J p+∑ j ∈ Finset.univ.filter (fun j => j < i),H j p
  have hF : ∀ i,ContDiff ℝ ∞ (F i) := by
    intro i
    exact hJ.add (ContDiff.sum (fun j _ => hH j))
  have he0 : ∀ i,ρ i (lo i)=0 := by
    intro i
    obtain ⟨ε,hε,hlo,_⟩ := hcol i
    exact hlo _ (by linarith)
  have he1 : ∀ i,ρ i (hi i)=1 := by
    intro i
    obtain ⟨ε,hε,_,hhi⟩ := hcol i
    exact hhi _ (by linarith)
  have hdis : Pairwise (fun i j : Fin N => Disjoint (Ioo (lo i.castSucc) (hi i.castSucc))
      (Ioo (lo j.castSucc) (hi j.castSucc))) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · apply Set.disjoint_left.mpr
      intro s hs ht
      have hh := hord i.castSucc j.castSucc (by simpa using hij)
      linarith [hs.2,ht.1]
    · apply Set.disjoint_left.mpr
      intro s hs ht
      have hh := hord j.castSucc i.castSucc (by simpa using hij)
      linarith [ht.2,hs.1]
  let G := surfaceFinalLayer (J ∘ planeMoments) (fun j => H j ∘ planeMoments) R
    (fun j => ρ j.castSucc) (ρ (Fin.last N))
  have hG : ContDiff ℝ ∞ G := surfaceFinalLayer_smooth (hJ.comp planeMoments_smooth) hR
    (fun j => (hH j).comp planeMoments_smooth) (fun j => (hsm j.castSucc).1) (hsm _).1
  have he : ∀ i : Fin N,∀ s∈Ioo (lo i.castSucc) (hi i.castSucc),∀ v,planeMoments v∈V →
      G (s,v)=layerHamiltonian (F i) (H i) (ρ i.castSucc) (s,v) := by
    intro i s hs v _
    exact hiso _ (J ∘ planeMoments) R (fun j => H j ∘ planeMoments) i s ⟨hs.1.le,hs.2.le⟩ v
  have hlo : ∀ i : Fin N,lo i.castSucc∈Ioo α β := fun i =>
    ⟨(hbd _).1,lt_trans (hbd _).2.1 (hbd _).2.2⟩
  have hhi : ∀ i : Fin N,hi i.castSucc∈Ioo α β := fun i =>
    ⟨lt_trans (hbd _).1 (hbd _).2.1,(hbd _).2.2⟩
  obtain ⟨U,φ,hU,hBU,hφ,hemb,him,hform,hd⟩ := finite_weighted_layer_packing hδ hsmall
    isOpen_Ioo (convex_Ioo _ _) hA hB hbase F H (fun i => ρ i.castSucc) hF hH
    (fun i => (hsm _).1) (fun i s => (hpos _ s).2.2) hV hHp
    (fun i => lo i.castSucc) (fun i => hi i.castSucc) r r' hlo hhi (fun i => (hbd _).2.1)
    (fun i => he0 i.castSucc) (fun i => he1 i.castSucc) hdis hr' hrr hsimplex hheight G hG he
  exact ⟨lo,hi,ρ,hbd,hord,hsm,hpos,hcol,U,φ,hU,hBU,hφ,hemb,him,hform,hd⟩


end

section
open scoped ContDiff Topology
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure CompactHamiltonianIsotopy (A : E →L[ℝ] E →L[ℝ] ℝ) where
  map : ℝ → E ≃ₜ E
  smooth : ContDiff ℝ ∞ (fun p : ℝ × E => map p.1 p.2)
  inverse_smooth : ContDiff ℝ ∞ (fun p : ℝ × E => (map p.1).symm p.2)
  zero : map 0 = Homeomorph.refl E
  hamiltonian : ℝ × E → ℝ
  hamiltonian_smooth : ContDiff ℝ ∞ hamiltonian
  compact : HasCompactSupport hamiltonian
  flow : ∀ t x, HasDerivAt (fun s => map s x)
    (hamiltonianField A hamiltonian (t,map t x)) t
  symplectic : ∀ t x v w, A (fderiv ℝ (map t) x v) (fderiv ℝ (map t) x w) = A v w
  fixed : ∀ t x, x ∉ Prod.snd '' tsupport hamiltonian → map t x = x

namespace CompactHamiltonianIsotopy
variable {A : E →L[ℝ] E →L[ℝ] ℝ}

@[fun_prop] theorem map_smooth (Φ : CompactHamiltonianIsotopy A) (t : ℝ) :
    ContDiff ℝ ∞ (Φ.map t) := Φ.smooth.comp (contDiff_const.prodMk contDiff_id)

@[fun_prop] theorem map_inverse_smooth (Φ : CompactHamiltonianIsotopy A) (t : ℝ) :
    ContDiff ℝ ∞ (Φ.map t).symm := Φ.inverse_smooth.comp (contDiff_const.prodMk contDiff_id)

theorem compact_displacement (Φ : CompactHamiltonianIsotopy A) (t : ℝ) :
    HasCompactSupport (fun x => Φ.map t x-x) :=
  HasCompactSupport.intro (Φ.compact.image continuous_snd)
    (fun x hx => sub_eq_zero.mpr (Φ.fixed t x hx))

end CompactHamiltonianIsotopy

end

section
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem homeomorph_pointwise_fderiv_isInvertible (f : E ≃ₜ E) {x : E}
    (hf : DifferentiableAt ℝ f x) (hi : DifferentiableAt ℝ f.symm (f x)) :
    (fderiv ℝ f x).IsInvertible := by
  have hleft : (fderiv ℝ f.symm (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E := by
    rw [←fderiv_comp x hi hf]
    simp only [show (f.symm : E → E) ∘ f = id by funext y; exact f.symm_apply_apply y]
    exact fderiv_id
  have hright : (fderiv ℝ f x).comp (fderiv ℝ f.symm (f x)) = ContinuousLinearMap.id ℝ E := by
    have hh := fderiv_comp (f x) (show DifferentiableAt ℝ f (f.symm (f x)) by simpa using hf) hi
    simp only [f.symm_apply_apply] at hh
    rw [←hh]
    simp only [show (f : E → E) ∘ f.symm = id by funext y; exact f.apply_symm_apply y]
    exact fderiv_id
  refine ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ f x) (fderiv ℝ f.symm (f x)) ?_ ?_,rfl⟩
  · intro v
    exact congrArg (fun L : E →L[ℝ] E => L v) hleft
  · intro v
    exact congrArg (fun L : E →L[ℝ] E => L v) hright


end

section
open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω : E →L[ℝ] E →L[ℝ] ℝ}

def hamiltonianBaseShear (Φ : CompactHamiltonianIsotopy Ω) (θ : ℝ → ℝ)
    (hθ : ContDiff ℝ ∞ θ) : (Plane × E) ≃ₜ (Plane × E) where
  toFun p := (p.1,Φ.map (θ p.1.1) p.2)
  invFun p := (p.1,(Φ.map (θ p.1.1)).symm p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk
    (Φ.smooth.continuous.comp ((hθ.continuous.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (Φ.inverse_smooth.continuous.comp ((hθ.continuous.comp (continuous_fst.comp continuous_fst)).prodMk continuous_snd))

@[fun_prop] theorem hamiltonianBaseShear_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (hamiltonianBaseShear Φ θ hθ) :=
  contDiff_fst.prodMk (Φ.smooth.comp
    ((hθ.comp (contDiff_fst.comp contDiff_fst)).prodMk contDiff_snd))

@[fun_prop] theorem hamiltonianBaseShear_inverse_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (hamiltonianBaseShear Φ θ hθ).symm :=
  contDiff_fst.prodMk (Φ.inverse_smooth.comp
    ((hθ.comp (contDiff_fst.comp contDiff_fst)).prodMk contDiff_snd))

theorem hamiltonianBaseShear_fderiv (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (p v : Plane × E) :
    fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p v =
      (v.1,(deriv θ p.1.1*v.1.1) • hamiltonianField Ω Φ.hamiltonian
        (θ p.1.1,Φ.map (θ p.1.1) p.2) + fderiv ℝ (Φ.map (θ p.1.1)) p.2 v.2) := by
  have hθd := (hθ.differentiable (by simp) p.1.1).hasDerivAt
  have htime := hθd.hasFDerivAt.comp p
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p.1)).comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p)))
  have hinner := htime.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hf := ((Φ.smooth.differentiable (by simp) (θ p.1.1,p.2)).hasFDerivAt.comp p hinner)
  have hh := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hf
  change HasFDerivAt (hamiltonianBaseShear Φ θ hθ) _ p at hh
  rw [hh.fderiv]
  change (v.1,fderiv ℝ (fun q : ℝ × E => Φ.map q.1 q.2) (θ p.1.1,p.2)
    (v.1.1*deriv θ p.1.1,v.2)) = _
  rw [joint_flow_fderiv Φ.smooth Φ.flow,mul_comm v.1.1]

theorem hamiltonianBaseShear_fderiv_isInvertible (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : Plane × E) :
    (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p).IsInvertible :=
  homeomorph_pointwise_fderiv_isInvertible _
    ((hamiltonianBaseShear_smooth Φ hθ).differentiable (by simp) p)
    ((hamiltonianBaseShear_inverse_smooth Φ hθ).differentiable (by simp) _)

def baseShearPrimitiveCoefficient (Φ : CompactHamiltonianIsotopy Ω) (θ : ℝ → ℝ)
    (p : ℝ × E) : ℝ := deriv θ p.1 * Φ.hamiltonian (θ p.1,Φ.map (θ p.1) p.2)

@[fun_prop] theorem baseShearPrimitiveCoefficient_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) : ContDiff ℝ ∞ (baseShearPrimitiveCoefficient Φ θ) := by
  exact ((hθ.deriv').comp contDiff_fst).mul
    (Φ.hamiltonian_smooth.comp ((hθ.comp contDiff_fst).prodMk
      (Φ.smooth.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd))))

theorem baseShearPrimitiveCoefficient_vertical (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (s : ℝ) (u v : E) :
    fderiv ℝ (baseShearPrimitiveCoefficient Φ θ) (s,u) (0,v) =
      deriv θ s * spatialDifferential Φ.hamiltonian (θ s,Φ.map (θ s) u)
        (fderiv ℝ (Φ.map (θ s)) u v) := by
  have hchain := (((baseShearPrimitiveCoefficient_smooth Φ hθ).differentiable (by simp) (s,u)).hasFDerivAt.comp u
    ((hasFDerivAt_const (𝕜 := ℝ) s u).prodMk (hasFDerivAt_id (𝕜 := ℝ) u))).fderiv
  have hdH := ((Φ.hamiltonian_smooth.differentiable (by simp) (θ s,Φ.map (θ s) u)).hasFDerivAt.comp u
    ((hasFDerivAt_const (𝕜 := ℝ) (θ s) u).prodMk ((Φ.map_smooth (θ s)).differentiable (by simp) u).hasFDerivAt)).const_mul (deriv θ s)
  have he := congrArg (fun L : E →L[ℝ] ℝ => L v) (hchain.symm.trans hdH.fderiv)
  simpa [baseShearPrimitiveCoefficient,spatialDifferential,mul_comm] using he



theorem hamiltonianBaseShear_suspension (hΩ : Ω.IsInvertible)
    (hskew : ∀ v w, Ω v w = -Ω w v) (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : Plane × E) :
    (Ω.bilinearComp (ContinuousLinearMap.snd ℝ Plane E) (ContinuousLinearMap.snd ℝ Plane E)).bilinearComp
      (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) =
    horizontalCoupling Ω (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ)) 0 p := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [firstBase_horizontalCoupling Ω (baseShearPrimitiveCoefficient_smooth Φ hθ),
    baseShearPrimitiveCoefficient_vertical Φ hθ,baseShearPrimitiveCoefficient_vertical Φ hθ]
  simp only [ContinuousLinearMap.bilinearComp_apply]
  change Ω (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p v).2
    (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p w).2 = _
  rw [hamiltonianBaseShear_fderiv Φ hθ,hamiltonianBaseShear_fderiv Φ hθ]
  dsimp only
  let X := hamiltonianField Ω Φ.hamiltonian (θ p.1.1,Φ.map (θ p.1.1) p.2)
  have hXX : Ω X X=0 := by have hh := hskew X X; linarith
  have hX (z : E) : Ω X z = -spatialDifferential Φ.hamiltonian
      (θ p.1.1,Φ.map (θ p.1.1) p.2) z := hamiltonianField_contraction hΩ _ _ z
  have hright (z : E) : Ω z X = spatialDifferential Φ.hamiltonian
      (θ p.1.1,Φ.map (θ p.1.1) p.2) z := by rw [hskew,hX,neg_neg]
  change Ω ((deriv θ p.1.1*v.1.1) • X+fderiv ℝ (Φ.map (θ p.1.1)) p.2 v.2)
      ((deriv θ p.1.1*w.1.1) • X+fderiv ℝ (Φ.map (θ p.1.1)) p.2 w.2) = _
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul,hXX,hX,hright,
    Φ.symplectic]
  ring



theorem baseShear_pullback_horizontal (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (g : Plane × E → ℝ) :
    staticPullbackOneForm (horizontalOneForm 0 g) (hamiltonianBaseShear Φ θ hθ) =
      horizontalOneForm 0 (g ∘ hamiltonianBaseShear Φ θ hθ) := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  simp only [staticPullbackOneForm,ContinuousLinearMap.comp_apply,horizontalOneForm_apply,
    Pi.zero_apply,zero_mul,zero_add,hamiltonianBaseShear_fderiv]
  rfl

theorem baseShear_coupling_pullback (hΩ : Ω.IsInvertible)
    (hskew : ∀ v w, Ω v w = -Ω w v) (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {g : Plane × E → ℝ} (hg : ContDiff ℝ ∞ g) (p : Plane × E) :
    (horizontalCoupling Ω 0 g (hamiltonianBaseShear Φ θ hθ p)).bilinearComp
      (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) =
      horizontalCoupling Ω (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ))
        (g ∘ hamiltonianBaseShear Φ θ hθ) p := by
  have hsplit : horizontalOneForm (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ))
      (g ∘ hamiltonianBaseShear Φ θ hθ) =
      horizontalOneForm (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ)) 0 +
        horizontalOneForm 0 (g ∘ hamiltonianBaseShear Φ θ hθ) := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    simp [horizontalOneForm_apply]
  have hnat := staticPullbackOneForm_exterior
    ((horizontalOneForm_smooth (A := 0) contDiff_const hg).contDiffAt (x := hamiltonianBaseShear Φ θ hθ p))
    ((hamiltonianBaseShear_smooth Φ hθ).contDiffAt (x := p))
  rw [baseShear_pullback_horizontal Φ hθ g] at hnat
  have hsum : euclideanExteriorOneForm
      (horizontalOneForm (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ))
        (g ∘ hamiltonianBaseShear Φ θ hθ)) p =
      euclideanExteriorOneForm (horizontalOneForm (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ)) 0) p +
        euclideanExteriorOneForm (horizontalOneForm 0 (g ∘ hamiltonianBaseShear Φ θ hθ)) p := by
    rw [hsplit]
    exact euclideanExteriorOneForm_add
      ((horizontalOneForm_smooth (firstBaseCoefficient_smooth (baseShearPrimitiveCoefficient_smooth Φ hθ)) contDiff_const).differentiable (by simp) p)
      ((horizontalOneForm_smooth contDiff_const (hg.comp (hamiltonianBaseShear_smooth Φ hθ))).differentiable (by simp) p)
  have hsusp := hamiltonianBaseShear_suspension hΩ hskew Φ hθ p
  have hadd (F G : (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ)
      (L : (Plane × E) →L[ℝ] (Plane × E)) :
      (F+G).bilinearComp L L=F.bilinearComp L L+G.bilinearComp L L := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [horizontalCoupling,hadd,←hnat,hsusp]
  simp only [horizontalCoupling,hsum]
  exact add_assoc _ _ _

theorem baseShear_coupling_isInvertible [FiniteDimensional ℝ E]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {g : ℝ × E → ℝ} (hg : ContDiff ℝ ∞ g) (p : Plane × E)
    (hpos : 0<fderiv ℝ g (p.1.1,Φ.map (θ p.1.1) p.2) (1,0)) :
    (horizontalCoupling Ω (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ))
      (firstBaseCoefficient g ∘ hamiltonianBaseShear Φ θ hθ) p).IsInvertible := by
  rw [←baseShear_coupling_pullback hΩ hskew Φ hθ (firstBaseCoefficient_smooth hg)]
  exact bilinearComp_isInvertible
    (secondBase_horizontalCoupling_isInvertible hΩ hg (hamiltonianBaseShear Φ θ hθ p) hpos)
    (hamiltonianBaseShear_fderiv_isInvertible Φ hθ p)



theorem baseShear_pullback_horizontal_general (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (A B : Plane × E → ℝ) :
    staticPullbackOneForm (horizontalOneForm A B) (hamiltonianBaseShear Φ θ hθ) =
      horizontalOneForm (A ∘ hamiltonianBaseShear Φ θ hθ) (B ∘ hamiltonianBaseShear Φ θ hθ) := by
  funext p
  apply ContinuousLinearMap.ext
  intro v
  simp only [staticPullbackOneForm,ContinuousLinearMap.comp_apply,horizontalOneForm_apply,
    hamiltonianBaseShear_fderiv]
  rfl

theorem baseShear_coupling_pullback_general (hΩ : Ω.IsInvertible)
    (hskew : ∀ v w, Ω v w = -Ω w v) (Φ : CompactHamiltonianIsotopy Ω)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {A B : Plane × E → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (p : Plane × E) :
    (horizontalCoupling Ω A B (hamiltonianBaseShear Φ θ hθ p)).bilinearComp
      (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) (fderiv ℝ (hamiltonianBaseShear Φ θ hθ) p) =
      horizontalCoupling Ω
        (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ) + A ∘ hamiltonianBaseShear Φ θ hθ)
        (B ∘ hamiltonianBaseShear Φ θ hθ) p := by
  have hnat := staticPullbackOneForm_exterior
    ((horizontalOneForm_smooth hA hB).contDiffAt (x := hamiltonianBaseShear Φ θ hθ p))
    ((hamiltonianBaseShear_smooth Φ hθ).contDiffAt (x := p))
  rw [baseShear_pullback_horizontal_general Φ hθ A B] at hnat
  have hsplit : horizontalOneForm
      (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ) + A ∘ hamiltonianBaseShear Φ θ hθ)
      (B ∘ hamiltonianBaseShear Φ θ hθ) =
      horizontalOneForm (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ)) 0 +
        horizontalOneForm (A ∘ hamiltonianBaseShear Φ θ hθ) (B ∘ hamiltonianBaseShear Φ θ hθ) := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    simp [horizontalOneForm_apply,add_mul,add_assoc]
  have hsum : euclideanExteriorOneForm
      (horizontalOneForm
        (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ) + A ∘ hamiltonianBaseShear Φ θ hθ)
        (B ∘ hamiltonianBaseShear Φ θ hθ)) p =
      euclideanExteriorOneForm (horizontalOneForm (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ)) 0) p +
        euclideanExteriorOneForm (horizontalOneForm (A ∘ hamiltonianBaseShear Φ θ hθ)
          (B ∘ hamiltonianBaseShear Φ θ hθ)) p := by
    rw [hsplit]
    exact euclideanExteriorOneForm_add
      ((horizontalOneForm_smooth (firstBaseCoefficient_smooth (baseShearPrimitiveCoefficient_smooth Φ hθ))
        (contDiff_const (c := (0 : ℝ)))).differentiable (by simp) p)
      ((horizontalOneForm_smooth (hA.comp (hamiltonianBaseShear_smooth Φ hθ))
        (hB.comp (hamiltonianBaseShear_smooth Φ hθ))).differentiable (by simp) p)
  have hsusp := hamiltonianBaseShear_suspension hΩ hskew Φ hθ p
  have hadd (F G : (Plane × E) →L[ℝ] (Plane × E) →L[ℝ] ℝ)
      (L : (Plane × E) →L[ℝ] (Plane × E)) :
      (F+G).bilinearComp L L=F.bilinearComp L L+G.bilinearComp L L := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [horizontalCoupling,hadd,←hnat,hsusp]
  simp only [horizontalCoupling,hsum]
  exact add_assoc _ _ _

theorem baseShear_weighted_isInvertible [FiniteDimensional ℝ E]
    (hΩ : Ω.IsInvertible) (hskew : ∀ v w, Ω v w = -Ω w v)
    (Φ : CompactHamiltonianIsotopy Ω) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {a b w : Plane → ℝ} {G : ℝ × E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w)
    (hG : ContDiff ℝ ∞ G) (p : Plane × E)
    (hbase : 0<fderiv ℝ b p.1 (1,0)-fderiv ℝ a p.1 (0,1))
    (hwzero : fderiv ℝ w p.1 (1,0)=0) (hwpos : 0≤w p.1)
    (hGpos : 0≤fderiv ℝ G (p.1.1,Φ.map (θ p.1.1) p.2) (1,0)) :
    (horizontalCoupling Ω
      (firstBaseCoefficient (baseShearPrimitiveCoefficient Φ θ) +
        baseCoefficient a ∘ hamiltonianBaseShear Φ θ hθ)
      (weightedSecondCoefficient b w G ∘ hamiltonianBaseShear Φ θ hθ) p).IsInvertible := by
  rw [←baseShear_coupling_pullback_general hΩ hskew Φ hθ (baseCoefficient_smooth ha)
    (weightedSecondCoefficient_smooth hb hw hG)]
  exact bilinearComp_isInvertible
    (weighted_horizontalCoupling_isInvertible hΩ ha hb hw hG
      (hamiltonianBaseShear Φ θ hθ p) hbase hwzero hwpos hGpos)
    (hamiltonianBaseShear_fderiv_isInvertible Φ hθ p)


end

open scoped ContDiff
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : E →L[ℝ] E →L[ℝ] ℝ}

def surfaceFirstPrimitive (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (H : E → ℝ) (a b w : Plane → ℝ) (p : ℝ × (Plane × E)) : (Plane × E) →L[ℝ] ℝ :=
  horizontalOneForm
    (fun x => a x.1 + p.1*deriv S x.1.1 *
      Φ.hamiltonian (p.1*S x.1.1,Φ.map (p.1*S x.1.1) x.2))
    (fun x => b x.1 + w x.1 * S x.1.1 * H ((Φ.map p.1).symm
      (Φ.map (p.1*S x.1.1) x.2))) p.2

@[fun_prop] theorem surfaceFirstPrimitive_smooth (Φ : CompactHamiltonianIsotopy Ω)
    {S : ℝ → ℝ} {H : E → ℝ} {a b w : Plane → ℝ}
    (hS : ContDiff ℝ ∞ S) (hH : ContDiff ℝ ∞ H)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (surfaceFirstPrimitive Φ S H a b w) := by
  have ht : ContDiff ℝ ∞ (fun p : ℝ × (Plane × E) => p.1*S p.2.1.1) :=
    contDiff_fst.mul (hS.comp ((contDiff_fst.comp contDiff_fst).comp contDiff_snd))
  have hq : ContDiff ℝ ∞ (fun p : ℝ × (Plane × E) => Φ.map (p.1*S p.2.1.1) p.2.2) :=
    Φ.smooth.comp (ht.prodMk (contDiff_snd.comp contDiff_snd))
  have hA : ContDiff ℝ ∞ (fun p : ℝ × (Plane × E) => a p.2.1 +
      p.1*deriv S p.2.1.1*Φ.hamiltonian (p.1*S p.2.1.1,Φ.map (p.1*S p.2.1.1) p.2.2)) :=
    (ha.comp (contDiff_fst.comp contDiff_snd)).add
      ((contDiff_fst.mul ((hS.deriv').comp ((contDiff_fst.comp contDiff_fst).comp contDiff_snd))).mul
        (Φ.hamiltonian_smooth.comp (ht.prodMk hq)))
  have hB : ContDiff ℝ ∞ (fun p : ℝ × (Plane × E) => b p.2.1 + w p.2.1*S p.2.1.1*
      H ((Φ.map p.1).symm (Φ.map (p.1*S p.2.1.1) p.2.2))) :=
    (hb.comp (contDiff_fst.comp contDiff_snd)).add
      (((hw.comp (contDiff_fst.comp contDiff_snd)).mul
        (hS.comp ((contDiff_fst.comp contDiff_fst).comp contDiff_snd))).mul
        (hH.comp (Φ.inverse_smooth.comp (contDiff_fst.prodMk hq))))
  exact (hA.smul contDiff_const).add (hB.smul contDiff_const)

theorem surfaceFirstPrimitive_zero (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (H : E → ℝ) (a b w : Plane → ℝ) (p : Plane × E) :
    surfaceFirstPrimitive Φ S H a b w (0,p)=
      horizontalOneForm (baseCoefficient a)
        (fun x => b x.1+w x.1*S x.1.1*H x.2) p := by
  apply ContinuousLinearMap.ext
  intro v
  simp [surfaceFirstPrimitive,horizontalOneForm_apply,baseCoefficient,Φ.zero]

theorem surfaceFirstPrimitive_lower (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (H : E → ℝ) (a b w : Plane → ℝ) (ℓ : ℝ) (p : Plane × E)
    (hS : S p.1.1=0) (hd : deriv S p.1.1=0) :
    surfaceFirstPrimitive Φ S H a b w (ℓ,p)=
      horizontalOneForm (baseCoefficient a) (baseCoefficient b) p := by
  apply ContinuousLinearMap.ext
  intro v
  simp [surfaceFirstPrimitive,horizontalOneForm_apply,baseCoefficient,hS,hd]

theorem surfaceFirstPrimitive_upper (Φ : CompactHamiltonianIsotopy Ω) (S : ℝ → ℝ)
    (H : E → ℝ) (a b w : Plane → ℝ) (ℓ : ℝ) (p : Plane × E)
    (hS : S p.1.1=1) (hd : deriv S p.1.1=0) :
    surfaceFirstPrimitive Φ S H a b w (ℓ,p)=
      horizontalOneForm (baseCoefficient a) (fun x => b x.1+w x.1*H x.2) p := by
  apply ContinuousLinearMap.ext
  intro v
  simp [surfaceFirstPrimitive,horizontalOneForm_apply,baseCoefficient,hS,hd]

variable {ι : Type*} [Fintype ι]

def surfaceInterpolatedLayer (S : ℝ → ℝ) (K H : E → ℝ) (h : ι → E → ℝ)
    (ψ : E → E) (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (τ : ℝ) (p : ℝ × E) : ℝ :=
  (1-τ)*surfaceFirstLayer S H ψ p +
    τ*surfaceFinalLayer (K-H) h (surfaceRemainder K H h ψ) ρ ρ₀ p

theorem surfaceInterpolatedLayer_endpoints (Φ : CompactHamiltonianIsotopy Ω)
    (S : ℝ → ℝ) (K H : E → ℝ) (h : ι → E → ℝ)
    (ρ : ι → ℝ → ℝ) (ρ₀ : ℝ → ℝ) (τ s : ℝ) (v : E) :
    (S s=0 → (∀ i, ρ i s=0) → ρ₀ s=0 →
      surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ τ (s,Φ.map (S s) v)=τ*(K v-H v)) ∧
    (S s=1 → (∀ i, ρ i s=1) → ρ₀ s=1 →
      surfaceInterpolatedLayer S K H h (Φ.map 1).symm ρ ρ₀ τ (s,Φ.map (S s) v)=
        H v+τ*(K v-H v)) := by
  constructor
  · intro hS hρ hρ₀
    simp [surfaceInterpolatedLayer,surfaceFirstLayer,surfaceFinalLayer_lower hρ hρ₀,
      hS,Φ.zero]
  · intro hS hρ hρ₀
    simp only [surfaceInterpolatedLayer,surfaceFirstLayer,surfaceFinalLayer_upper hρ hρ₀,
      hS,Homeomorph.symm_apply_apply,one_mul]
    ring



end PackingSufficiencySupport.Hamiltonian
end

end OAI
