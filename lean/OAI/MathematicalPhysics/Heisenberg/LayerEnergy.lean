import OAI.MathematicalPhysics.Heisenberg.ReturnConditioning

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical

@[reducible] local instance exposureDecEq (α : Type*) : DecidableEq α := Classical.decEq α

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.Conditioning
variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma layerExposure_equivalence {T : Type*} [Fintype T] (s : Equiv.Perm T)
    (τ : T → Equiv.Perm V) (P : Set (T×V)) : Equivalence (layerExposure s τ P) := by
  constructor
  · intro b
    exact ⟨fun _ _ => rfl,rfl⟩
  · intro b c h
    refine ⟨?_,h.2.symm⟩
    intro z hz
    exact (h.1 z (h.2 ▸ hz)).symm
  · intro b c d hbc hcd
    refine ⟨?_,hcd.2.trans hbc.2⟩
    intro z hz
    exact (hbc.1 z hz).trans (hcd.1 z (hbc.2.symm ▸ hz))

lemma residual_integral {n : ℕ} (w : Fin n → Bool → ℝ)
    (hw : ∀ i,∑ b,w i b=1) (M : Fin n → Prop) (base : Fin n → Bool)
    (F : (Fin n → Bool) → ℝ) :
    (∑ c : Fin n → Bool,productWeight w c * F (residualCoins M base c)) =
      ∑ c : {i // ¬M i} → Bool,productWeight (fun i : {i // ¬M i} => w i) c *
        F (merge M (fun i => base i) c) := by
  let e := Equiv.piEquivPiSubtypeProd M (fun _ => Bool)
  rw [←e.symm.sum_comp,Fintype.sum_prod_type]
  have hr (a : {i // M i} → Bool) (c : {i // ¬M i} → Bool) :
      residualCoins M base (merge M a c)=merge M (fun i => base i) c := by
    funext i
    by_cases hi : M i
    · simp [residualCoins,hi,merge]
    · simp [residualCoins,hi,merge]
  change (∑ a : {i // M i} → Bool, ∑ c : {i // ¬M i} → Bool,
    productWeight w (merge M a c)*F (residualCoins M base (merge M a c))) = _
  simp_rw [hr,productWeight_merge,mul_assoc,←Finset.mul_sum]
  have hs : (∑ a : {i // M i} → Bool, productWeight (fun i : {i // M i} => w i) a) = 1 := by
    convert productWeight_sum (fun i : {i // M i} => w i) (fun i => hw i) using 1
    congr 1
    ext c
    simp
  rw [←Finset.sum_mul, hs, one_mul]

theorem layer_exposure_full {n : ℕ} (s : Equiv.Perm (Fin n))
    (τ : Fin n → Equiv.Perm V) (w : Fin n → Bool → ℝ) (hw : ∀ i,∑ b,w i b=1)
    (P : Set (Fin n×V)) (base : Fin n → Bool) (F : (Fin n → Bool) → ℝ) :
    let A := MissingSet (layerHistory s τ base) P
    let M := layerRevealed τ A
    let c₀ := (2:ℝ)^missingCount (layerHistory s τ base) P *
      productWeight (fun i : {i // M i} => w i) (fun i => base i)
    (∑ c : Fin n → Bool,if layerExposure s τ P base c then
      productWeight w c*(2:ℝ)^missingCount (layerHistory s τ c) P*F c else 0) =
      c₀ * ∑ c : Fin n → Bool,if OutsideHit (layerHistory s τ (residualCoins M base c)) P A
        then productWeight w c*F (residualCoins M base c) else 0 := by
  dsimp only
  have he := layer_exposure_disintegration s τ w P base F
  have hu : @Finset.univ (Fin n → Bool)
    (@Pi.instFintype (Fin n) (fun _ => Bool) (fun a b => Classical.propDecidable (a=b))
      (Fin.fintype n) (fun _ => Bool.fintype)) = (Finset.univ : Finset (Fin n → Bool)) := by
    ext c
    simp
  rw [hu] at he
  refine he.trans ?_
  congr 1
  have h := residual_integral w hw
    (layerRevealed τ (MissingSet (layerHistory s τ base) P)) base
    (fun c => if OutsideHit (layerHistory s τ c) P (MissingSet (layerHistory s τ base) P)
      then F c else 0)
  simp only [mul_ite,mul_zero] at h
  convert h.symm using 1
  congr 1
  ext c
  simp

theorem conditional_layer_exposure {n : ℕ} (s : Equiv.Perm (Fin n))
    (τ : Fin n → Equiv.Perm V) (w : Fin n → Bool → ℝ)
    (hw : ∀ i,∑ b,w i b=1) (hw0 : ∀ i b,0≤w i b)
    (P : Set (Fin n×V)) (base : Fin n → Bool) (F : (Fin n → Bool) → ℝ)
    (hbase : productWeight w base≠0) :
    let A := MissingSet (layerHistory s τ base) P
    let M := layerRevealed τ A
    let σ := fun c => layerHistory s τ (residualCoins M base c)
    let μ := fun c => productWeight w c*(2:ℝ)^missingCount (layerHistory s τ c) P
    conditional μ (layerExposure s τ P) F base =
      (∑ c : Fin n → Bool,if OutsideHit (σ c) P A then
        productWeight w c*F (residualCoins M base c) else 0)/
      (∑ c : Fin n → Bool,if OutsideHit (σ c) P A then productWeight w c else 0) := by
  dsimp only
  let μ := fun c => productWeight w c*(2:ℝ)^missingCount (layerHistory s τ c) P
  have hμ : ∀ c,0≤μ c := by
    intro c
    exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw0 i (c i))) (by positivity)
  have hm : 0 < mass μ (layerExposure s τ P) base := lt_of_lt_of_le
    (mul_pos (lt_of_le_of_ne (Finset.prod_nonneg (fun i _ => hw0 i (base i))) (Ne.symm hbase))
      (by positivity))
    (weight_le_mass μ hμ _ (layerExposure_equivalence s τ P).refl base)
  have hden := layer_exposure_full s τ w hw P base (fun _ => 1)
  simp only [mul_one] at hden
  change mass μ (layerExposure s τ P) base = _ at hden
  have hq := left_ne_zero_of_mul (hden ▸ ne_of_gt hm)
  rw [conditional,layer_exposure_full s τ w hw P base F]
  change (_*_) / mass μ (layerExposure s τ P) base = _
  rw [hden]
  exact mul_div_mul_left _ _ hq

end Heisenberg.Exposure

open Filter Topology
open scoped RealInnerProductSpace Classical
namespace Heisenberg.MeshEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
abbrev Op := E →L[ℝ] E

variable [CompleteSpace E]

lemma square_derivative {F : ℝ → Op (E:=E)} {D : Op (E:=E)}
    (h0 : F 0 = 1) (hD : HasDerivAt F D 0) :
    HasDerivAt (fun t => (ContinuousLinearMap.adjoint (F t)) * F t)
      (ContinuousLinearMap.adjoint D + D) 0 := by
  have ha := (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=E) (F:=E)).toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt 0 hD
  change HasDerivAt (fun t => ContinuousLinearMap.adjoint (F t)) (ContinuousLinearMap.adjoint D) 0 at ha
  have hh := ha.clm_comp hD
  change HasDerivAt (fun t => (ContinuousLinearMap.adjoint (F t))*F t)
    ((ContinuousLinearMap.adjoint D)*F 0 + (ContinuousLinearMap.adjoint (F 0))*D) 0 at hh
  simpa only [h0,ContinuousLinearMap.adjoint_one,one_mul,mul_one] using hh

theorem uniform_energy_error {F : ℝ → Op (E:=E)} {D : Op (E:=E)}
    (h0 : F 0 = 1) (hD : HasDerivAt F D 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ v : E,
      |‖F t v‖^2 - ‖v‖^2 - 2*t*⟪v,D v⟫| ≤ ε*|t| *‖v‖^2 := by
  have hh := (square_derivative h0 hD).isLittleO.def hε
  filter_upwards [hh] with t ht
  intro v
  let R : Op (E:=E) := (ContinuousLinearMap.adjoint (F t))*F t - 1 -
    t • (ContinuousLinearMap.adjoint D + D)
  have hR : ‖R‖ ≤ ε*|t| := by
    simpa only [h0,sub_zero,ContinuousLinearMap.adjoint_one,mul_one,
      Real.norm_eq_abs] using ht
  have he : ⟪v,R v⟫ = ‖F t v‖^2 - ‖v‖^2 - 2*t*⟪v,D v⟫ := by
    simp only [R,_root_.sub_apply,mul_apply_eq_comp,
      one_apply_eq_self,_root_.smul_apply,
      _root_.add_apply,inner_sub_right,inner_smul_right,
      inner_add_right,ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq,
      real_inner_comm (D v) v]
    ring
  rw [← he]
  calc
    _ ≤ ‖v‖ * ‖R v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖R‖*‖v‖) := mul_le_mul_of_nonneg_left (R.le_opNorm v) (norm_nonneg _)
    _ ≤ ‖v‖ * ((ε*|t|)*‖v‖) := by gcongr
    _ = _ := by ring

theorem finite_uniform_energy_error {I : Type*} [Finite I]
    (F : I → ℝ → Op (E:=E)) (D : I → Op (E:=E))
    (h0 : ∀ i, F i 0 = 1) (hD : ∀ i, HasDerivAt (F i) (D i) 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ i v,
      |‖F i t v‖^2 - ‖v‖^2 - 2*t*⟪v,D i v⟫| ≤ ε*|t| *‖v‖^2 := by
  exact Filter.eventually_all.mpr fun i => uniform_energy_error (h0 i) (hD i) hε

def sweep (D : ℕ → Op (E:=E)) : ℕ → ℝ → Op (E:=E)
  | 0, _ => 1
  | n+1, t => (1+t • D n) * sweep D n t

omit [CompleteSpace E] in
@[simp] lemma sweep_zero (D : ℕ → Op (E:=E)) (n : ℕ) : sweep D n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sweep,ih]

omit [CompleteSpace E] in
lemma sweep_derivative (D : ℕ → Op (E:=E)) (n : ℕ) :
    HasDerivAt (sweep D n) (∑ i ∈ Finset.range n, D i) 0 := by
  induction n with
  | zero => simpa [sweep] using hasDerivAt_const (0:ℝ) (1 : Op (E:=E))
  | succ n ih =>
    have hd : HasDerivAt (fun t : ℝ => (1:Op (E:=E))+t • D n) (D n) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const (D n) |>.const_add 1
    have hh := hd.clm_comp ih
    change HasDerivAt (sweep D (n+1)) (D n * sweep D n 0 +
      (1+(0:ℝ) • D n) * (∑ i ∈ Finset.range n, D i)) 0 at hh
    simpa only [sweep_zero,zero_smul,add_zero,zero_add,mul_one,one_mul,Finset.sum_range_succ,add_comm] using hh

end Heisenberg.MeshEnergy
namespace Heisenberg.MeshPair
open MeshEnergy
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def generator (w : E) : E →L[ℝ] E := (-1/2:ℝ) • (innerSL ℝ w).smulRight w

lemma generator_apply (w v : E) : generator w v = (-⟪w,v⟫/2) • w := by
  simp only [generator,_root_.smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]
  congr 1
  ring

lemma generator_energy (w v : E) : -⟪v,generator w v⟫ = (1/2:ℝ)*⟪w,v⟫^2 := by
  rw [generator_apply,inner_smul_right,real_inner_comm v w]
  ring

lemma step_norm_square (w v : E) (t : ℝ) :
    ‖(1+t • generator w) v‖^2 =
      ‖v‖^2-t*⟪w,v⟫^2+(t^2/4)*⟪w,v⟫^2*‖w‖^2 := by
  simp only [_root_.add_apply,one_apply_eq_self,_root_.smul_apply,generator_apply,smul_smul,norm_add_sq_real,
    inner_smul_right,real_inner_comm v w,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

lemma step_contraction (w : E) (hw : ‖w‖^2 ≤ 2) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1+t • generator w : E →L[ℝ] E)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [step_norm_square]
  have hsmall : t^2/4*‖w‖^2 ≤ t := by
    have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ t^2/4 by positivity)
    have hh' : t^2 ≤ t := by nlinarith
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ⟪w,v⟫)
  nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeVector (I : Set V) (a b : V) : EuclideanSpace ℝ V :=
  EuclideanSpace.single a (if a ∈ I then 1 else 0) -
    EuclideanSpace.single b (if b ∈ I then 1 else 0)

lemma edge_inner (I : Set V) (a b : V) (v : EuclideanSpace ℝ V) :
    ⟪edgeVector I a b,v⟫ = (if a ∈ I then v.ofLp a else 0) -
      (if b ∈ I then v.ofLp b else 0) := by
  simp only [edgeVector,inner_sub_left,EuclideanSpace.inner_single_left]
  split_ifs <;> simp

lemma edge_norm (I : Set V) {a b : V} (hab : a ≠ b) : ‖edgeVector I a b‖^2 ≤ 2 := by
  rw [← real_inner_self_eq_norm_sq,edge_inner]
  simp only [edgeVector,PiLp.sub_apply,PiLp.single_apply]
  split_ifs <;> simp_all
  norm_num

theorem sweep_dirichlet (I : Set V) (a b : ℕ → V) (n : ℕ)
    (v : EuclideanSpace ℝ V) :
    -⟪v,(∑ i ∈ Finset.range n, generator (edgeVector I (a i) (b i))) v⟫ =
      (1/2:ℝ) * ∑ i ∈ Finset.range n,
        ((if a i ∈ I then v.ofLp (a i) else 0) -
          (if b i ∈ I then v.ofLp (b i) else 0))^2 := by
  simp only [_root_.sum_apply,inner_sum,← Finset.sum_neg_distrib,
    generator_energy,edge_inner,Finset.mul_sum]

theorem sweep_energy (I : Set V) (a b : ℕ → V) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ v : EuclideanSpace ℝ V,
      |‖sweep (fun i => generator (edgeVector I (a i) (b i))) n t v‖^2 - ‖v‖^2 +
        t * ∑ i ∈ Finset.range n,
          ((if a i ∈ I then v.ofLp (a i) else 0) -
            (if b i ∈ I then v.ofLp (b i) else 0))^2| ≤ ε*|t| * ‖v‖^2 := by
  have hh := uniform_energy_error (sweep_zero (fun i => generator (edgeVector I (a i) (b i))) n)
    (sweep_derivative (fun i => generator (edgeVector I (a i) (b i))) n) hε
  filter_upwards [hh] with t ht
  intro v
  have he := sweep_dirichlet I a b n v
  convert ht v using 1
  congr 1
  nlinarith [congrArg (fun z : ℝ => t*z) he]

end Heisenberg.MeshPair
end

end OAI
