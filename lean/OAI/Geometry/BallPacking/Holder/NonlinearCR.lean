import Mathlib
import OAI.Geometry.BallPacking.Holder.BanachSpace

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter

 def ThirdHolderOn {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F]
    (f : X → F) (s : Set X) (H : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ‖f x-f y‖ ≤ H*‖x-y‖^((1:ℝ)/3)

 theorem thirdHolderOn_of_bounded_lipschitz {X F : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup F]
    {f : X → F} {s : Set X} {A L : ℝ} (hA : 0≤A) (hL : 0≤L)
    (hb : ∀ x ∈ s, ‖f x‖ ≤ A) (hl : ∀ x ∈ s, ∀ y ∈ s, ‖f x-f y‖ ≤ L*‖x-y‖) :
    ThirdHolderOn f s (2*A+L) := by
  intro x hx y hy
  have hr : 0≤‖x-y‖^((1:ℝ)/3) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hd : ‖x-y‖≤1
  · have hh := Real.self_le_rpow_of_le_one (norm_nonneg (x-y)) hd (show (1:ℝ)/3≤1 by norm_num)
    exact (hl x hx y hy).trans ((mul_le_mul_of_nonneg_left hh hL).trans
      (mul_le_mul_of_nonneg_right (by linarith) hr))
  · have hh := Real.one_le_rpow (le_of_not_ge hd) (show (0:ℝ)≤1/3 by norm_num)
    have hnorm : ‖f x-f y‖ ≤ 2*A := (norm_sub_le _ _).trans (by linarith [hb x hx,hb y hy])
    have hmul := mul_le_mul_of_nonneg_left hh (show 0≤2*A+L by positivity)
    nlinarith

namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev HMap (D E : Type*) [MetricSpace D] [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Holder D E ((1:ℝ)/3)

abbrev COne (D E : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] := COneHolder (E := E) D ((1:ℝ)/3)

def ofBoundedDeriv (f : D → F) (hf : Differentiable ℝ f) (M L : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hval : ∀ x, ‖f x‖ ≤ M)
    (hder : ∀ x, ‖fderiv ℝ f x‖ ≤ L) : HMap D F :=
  ofBound f hf.continuous M (2*M+L) hval (by positivity) (by
    intro x y
    rw [dist_eq_norm]
    exact thirdHolderOn_of_bounded_lipschitz hM hL (fun z _ => hval z)
      (fun z _ w _ => norm_sub_le_of_deriv_bound hf hder z w) x (mem_univ x) y (mem_univ y))

@[simp] lemma ofBoundedDeriv_value (f : D → F) (hf : Differentiable ℝ f) (M L : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hval : ∀ x, ‖f x‖ ≤ M)
    (hder : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (x : D) :
    valueCLM _ (ofBoundedDeriv f hf M L hM hL hval hder) x = f x := rfl

lemma ofBoundedDeriv_norm_le (f : D → F) (hf : Differentiable ℝ f) (M L : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hval : ∀ x, ‖f x‖ ≤ M)
    (hder : ∀ x, ‖fderiv ℝ f x‖ ≤ L) :
    ‖ofBoundedDeriv f hf M L hM hL hval hder‖ ≤ 2*M+L := by
  unfold ofBoundedDeriv
  apply (ofBound_norm_le _ _ _ _ hM _ _ _).trans
  exact max_le (by linarith) le_rfl

lemma holder_norm_le_of_deriv_bounds (u : HMap D F)
    (hu : Differentiable ℝ (valueCLM _ u)) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hval : ∀ x, ‖valueCLM _ u x‖ ≤ M)
    (hder : ∀ x, ‖fderiv ℝ (valueCLM _ u) x‖ ≤ L) : ‖u‖ ≤ 2*M+L := by
  have he : u = ofBoundedDeriv (valueCLM _ u) hu M L hM hL hval hder := by
    apply value_ext
    intro x
    rfl
  rw [he]
  exact ofBoundedDeriv_norm_le _ _ _ _ _ _ _ _

def cValue (u : COne D E) : D →ᵇ E := valueCLM _ (jetValueCLM _ u)
def cDeriv (u : COne D E) : D →ᵇ (D →L[ℝ] E) := valueCLM _ (jetDerivCLM _ u)

lemma c_hasFDerivAt (u : COne D E) (x : D) : HasFDerivAt (cValue u) (cDeriv u x) x :=
  hasFDerivAt u x

lemma c_differentiable (u : COne D E) : Differentiable ℝ (cValue u) :=
  fun x => (c_hasFDerivAt u x).differentiableAt

lemma c_fderiv (u : COne D E) (x : D) : fderiv ℝ (cValue u) x = cDeriv u x :=
  (c_hasFDerivAt u x).fderiv

lemma c_value_bound (u : COne D E) (x : D) : ‖cValue u x‖ ≤ ‖u‖ := jet_norm_value_le u x
lemma c_deriv_bound (u : COne D E) (x : D) : ‖cDeriv u x‖ ≤ ‖u‖ := jet_norm_deriv_le u x

@[simp] lemma cValue_add (u v : COne D E) (x : D) : cValue (u+v) x = cValue u x+cValue v x := rfl
@[simp] lemma cValue_smul (c : ℝ) (u : COne D E) (x : D) : cValue (c • u) x = c • cValue u x := rfl

section Superposition
variable {f : E → F} (hf : BoundedCThree f)
  {b : D → E} (hb : Differentiable ℝ b) {B : ℝ} (hB : 0 ≤ B)
  (hbB : ∀ x, ‖fderiv ℝ b x‖ ≤ B)

include hb hbB in
lemma base_fderiv_bound (u : COne D E) (x : D) :
    ‖fderiv ℝ (fun z => b z+cValue u z) x‖ ≤ B + ‖u‖ := by
  have hd : HasFDerivAt (fun z => b z+cValue u z) (fderiv ℝ b x+cDeriv u x) x := by
    convert! (hb x).hasFDerivAt.add (c_hasFDerivAt u x) using 1
  rw [hd.fderiv]
  exact (norm_add_le _ _).trans (add_le_add (hbB x) (c_deriv_bound u x))

include hf hb in
lemma superpose_differentiable (u : COne D E) :
    Differentiable ℝ (fun z => f (b z+cValue u z)) :=
  (hf.smooth.differentiable (by simp)).comp (hb.add (c_differentiable u))

include hb hbB in
lemma superpose_fderiv_bound (u : COne D E) (x : D) :
    ‖fderiv ℝ (fun z => f (b z+cValue u z)) x‖ ≤ hf.bound * (B+‖u‖) := by
  have hd : HasFDerivAt (fun z => f (b z+cValue u z))
      ((fderiv ℝ f (b x+cValue u x)).comp (fderiv ℝ b x+cDeriv u x)) x := by
    convert! ((hf.smooth.differentiable (by simp) (b x+cValue u x)).hasFDerivAt.comp x
      ((hb x).hasFDerivAt.add (c_hasFDerivAt u x))) using 1
  rw [hd.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hf.norm_fderiv_le _) ((norm_add_le _ _).trans
      (add_le_add (hbB x) (c_deriv_bound u x))) (norm_nonneg _) hf.bound_nonneg)

def superpose (u : COne D E) : HMap D F :=
  ofBoundedDeriv (fun z => f (b z+cValue u z)) (superpose_differentiable hf hb u)
    hf.bound (hf.bound*(B+‖u‖)) hf.bound_nonneg
    (mul_nonneg hf.bound_nonneg (add_nonneg hB (norm_nonneg u)))
    (fun x => hf.norm_le (b x+cValue u x)) (superpose_fderiv_bound hf hb hbB u)

@[simp] lemma superpose_value (u : COne D E) (x : D) :
    valueCLM _ (superpose hf hb hB hbB u) x = f (b x+cValue u x) := rfl

include hf hb in
lemma coefficient_differentiable (u : COne D E) :
    Differentiable ℝ (fun z => fderiv ℝ f (b z+cValue u z)) :=
  (hf.fderiv_smooth.differentiable (by simp)).comp (hb.add (c_differentiable u))

include hb hbB in
lemma coefficient_fderiv_bound (u : COne D E) (x : D) :
    ‖fderiv ℝ (fun z => fderiv ℝ f (b z+cValue u z)) x‖ ≤ hf.bound * (B+‖u‖) := by
  have hd : HasFDerivAt (fun z => fderiv ℝ f (b z+cValue u z))
      ((fderiv ℝ (fderiv ℝ f) (b x+cValue u x)).comp
        (fderiv ℝ (fun z => b z+cValue u z) x)) x := by
    convert! ((hf.fderiv_smooth.differentiable (by simp) _).hasFDerivAt.comp x
      (((hb.add (c_differentiable u)) x).hasFDerivAt)) using 1
  rw [hd.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hf.norm_fderiv₂_le _) (base_fderiv_bound hb hbB u x)
      (norm_nonneg _) hf.bound_nonneg)

def coefficient (u : COne D E) : HMap D (E →L[ℝ] F) :=
  ofBoundedDeriv (fun z => fderiv ℝ f (b z+cValue u z))
    (coefficient_differentiable hf hb u) hf.bound (hf.bound*(B+‖u‖))
    hf.bound_nonneg (by positivity [hf.bound_nonneg])
    (fun x => hf.norm_fderiv_le _) (coefficient_fderiv_bound hf hb hbB u)

@[simp] lemma coefficient_value (u : COne D E) (x : D) :
    valueCLM _ (coefficient hf hb hB hbB u) x = fderiv ℝ f (b x+cValue u x) := rfl

def superposeDeriv (u : COne D E) : COne D E →L[ℝ] HMap D F :=
  (bilinCLM (ContinuousLinearMap.apply ℝ F).flip (coefficient hf hb hB hbB u)).comp
    (jetValueCLM _)

@[simp] lemma superposeDeriv_value (u h : COne D E) (x : D) :
    valueCLM _ (superposeDeriv hf hb hB hbB u h) x =
      fderiv ℝ f (b x+cValue u x) (cValue h x) := rfl

include hf hb in
lemma variation_differentiable (u h : COne D E) :
    Differentiable ℝ (fun z => fderiv ℝ f (b z+cValue u z) (cValue h z)) :=
  (coefficient_differentiable hf hb u).clm_apply (c_differentiable h)

lemma superpose_remainder_norm (u h : COne D E) :
    ‖superpose hf hb hB hbB (u+h) - superpose hf hb hB hbB u -
      superposeDeriv hf hb hB hbB u h‖ ≤ hf.bound*(3+B+‖u‖)*‖h‖^2 := by
  let r := superpose hf hb hB hbB (u+h) - superpose hf hb hB hbB u -
      superposeDeriv hf hb hB hbB u h
  have hv : (valueCLM _ r : D → F) = fun z =>
      f ((b z+cValue u z)+cValue h z)-f (b z+cValue u z)-
        fderiv ℝ f (b z+cValue u z) (cValue h z) := by
    funext z
    simp only [r, map_sub, BoundedContinuousFunction.sub_apply, superpose_value,
      superposeDeriv_value, cValue_add, add_assoc]
  have hd : Differentiable ℝ (valueCLM _ r) := by
    rw [hv]
    exact ((hf.smooth.differentiable (by simp)).comp
      ((hb.add (c_differentiable u)).add (c_differentiable h))).sub
      (superpose_differentiable hf hb u) |>.sub (variation_differentiable hf hb u h)
  have hb0 (x : D) : ‖valueCLM _ r x‖ ≤ hf.bound * ‖h‖^2 := by
    rw [hv]
    exact (hf.remainder_bound _ _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (c_value_bound h x) 2) hf.bound_nonneg)
  have hb1 (x : D) : ‖fderiv ℝ (valueCLM _ r) x‖ ≤
      hf.bound * (B+‖u‖+1) * ‖h‖^2 := by
    rw [hv]
    apply (norm_fderiv_composed_remainder hf ((hb.add (c_differentiable u)) x)
      (c_differentiable h x)).trans
    calc
      _ ≤ hf.bound * ‖h‖^2 * (B+‖u‖) + hf.bound * ‖h‖ * ‖h‖ := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (c_value_bound h x) 2) hf.bound_nonneg)
            (base_fderiv_bound hb hbB u x) (norm_nonneg _) (by positivity [hf.bound_nonneg])
        · rw [c_fderiv]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (c_value_bound h x) hf.bound_nonneg)
            (c_deriv_bound h x) (norm_nonneg _) (by positivity [hf.bound_nonneg])
      _ = _ := by ring
  have hh := holder_norm_le_of_deriv_bounds r hd
    (show 0 ≤ hf.bound * ‖h‖^2 by positivity [hf.bound_nonneg])
    (show 0 ≤ hf.bound * (B+‖u‖+1) * ‖h‖^2 by positivity [hf.bound_nonneg]) hb0 hb1
  convert! hh using 1; ring

local instance : NormedAddCommGroup (COne D E) := inferInstance
local instance : NormedSpace ℝ (COne D E) := inferInstance
local instance : NormedAddCommGroup (HMap D F) := inferInstance
local instance : NormedSpace ℝ (HMap D F) := inferInstance

lemma superpose_hasFDerivAt (u : COne D E) :
    HasFDerivAt (superpose hf hb hB hbB) (superposeDeriv hf hb hB hbB u) u := by
  have hC : 0 ≤ hf.bound * (3+B+‖u‖) := by positivity [hf.bound_nonneg]
  have hr : ∀ h : COne D E,
      ‖superpose (D := D) hf hb hB hbB (u+h) - superpose hf hb hB hbB u -
        superposeDeriv hf hb hB hbB u h‖ ≤ hf.bound * (3+B+‖u‖) * ‖h‖^2 :=
    superpose_remainder_norm (D := D) hf hb hB hbB u
  exact hasFDerivAt_of_quadratic_remainder (E := COne D E) (F := HMap D F)
    (g := superpose (D := D) hf hb hB hbB)
    (superposeDeriv (D := D) hf hb hB hbB u) u hC hr

end Superposition
end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ D] in
lemma mapCLM_norm_le (L : E →L[ℝ] F) (u : HMap D E) :
    ‖mapCLM ((1:ℝ)/3) L u‖ ≤ ‖L‖ * ‖u‖ := by
  apply (norm_le_of_bounds (mapCLM ((1:ℝ)/3) L u) (by positivity) (by positivity) ?_ ?_).trans
    (max_self _).le
  · intro x
    rw [mapCLM_value]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_value_le u x) (norm_nonneg L))
  · intro x y
    simp only [mapCLM_value, ← map_sub]
    exact (L.le_opNorm _).trans (by
      calc
        _ ≤ ‖L‖ * (‖u‖ * dist x y ^ ((1:ℝ)/3)) :=
          mul_le_mul_of_nonneg_left (norm_sub_value_le u x y) (norm_nonneg L)
        _ = _ := by ring)

def mapJet (L : E →L[ℝ] F) (u : COne D E) : COne D F :=
  ⟨(mapCLM _ L (jetValueCLM _ u),
    mapCLM _ ((ContinuousLinearMap.compL ℝ D E F) L) (jetDerivCLM _ u)), by
      intro x
      convert! L.hasFDerivAt.comp x (c_hasFDerivAt u x) using 1⟩

@[simp] lemma mapJet_value (L : E →L[ℝ] F) (u : COne D E) (x : D) :
    cValue (mapJet L u) x = L (cValue u x) := rfl

@[simp] lemma mapJet_deriv (L : E →L[ℝ] F) (u : COne D E) (x : D) :
    cDeriv (mapJet L u) x = L.comp (cDeriv u x) := rfl

lemma cValue_ext {u v : COne D E} (h : ∀ x, cValue u x = cValue v x) : u = v := by
  apply Subtype.ext
  apply Prod.ext
  · apply value_ext
    exact h
  · apply value_ext
    intro x
    have he : (cValue u : D → E) = cValue v := funext h
    change cDeriv u x = cDeriv v x
    rw [← c_fderiv u x, ← c_fderiv v x, he]

lemma mapJet_norm_le (L : E →L[ℝ] F) (u : COne D E) : ‖mapJet L u‖ ≤ ‖L‖*‖u‖ := by
  change max ‖mapCLM _ L (jetValueCLM _ u)‖
    ‖mapCLM _ ((ContinuousLinearMap.compL ℝ D E F) L) (jetDerivCLM _ u)‖ ≤ _
  apply max_le
  · exact (mapCLM_norm_le L _).trans
      (mul_le_mul_of_nonneg_left (jetValue_norm_le u) (norm_nonneg L))
  · apply (mapCLM_norm_le _ _).trans
    apply mul_le_mul _ (jetDeriv_norm_le u) (norm_nonneg _) (norm_nonneg L)
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro A
    exact ContinuousLinearMap.opNorm_comp_le L A

local instance : NormedAddCommGroup (COne D E) := inferInstance
local instance : NormedSpace ℝ (COne D E) := inferInstance
local instance : NormedAddCommGroup (COne D F) := inferInstance
local instance : NormedSpace ℝ (COne D F) := inferInstance
local instance : NormedAddCommGroup (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (COne D E →L[ℝ] COne D F) := ContinuousLinearMap.toNormedSpace

def mapJetBilinear : (E →L[ℝ] F) →L[ℝ] COne D E →L[ℝ] COne D F :=
  LinearMap.mkContinuous₂
    { toFun := fun L =>
        { toFun := mapJet (D := D) L
          map_add' := fun u v => by
            apply cValue_ext
            intro x
            simp only [mapJet_value, cValue_add, map_add]
          map_smul' := fun c u => by
            apply cValue_ext
            intro x
            simp only [mapJet_value, cValue_smul, map_smul, RingHom.id_apply] }
      map_add' := fun L M => by
        apply LinearMap.ext
        intro u
        apply cValue_ext
        intro x
        rfl
      map_smul' := fun c L => by
        apply LinearMap.ext
        intro u
        apply cValue_ext
        intro x
        rfl }
    1 (by intro L u; convert! mapJet_norm_le L u using 1; simp only [one_mul])

@[simp] lemma mapJetBilinear_value (L : E →L[ℝ] F) (u : COne D E) (x : D) :
    cValue (mapJetBilinear (D := D) (E := E) (F := F) L u) x = L (cValue u x) := rfl

def ofBoundedCThree {f : D → E} (hf : BoundedCThree f) : COne D E :=
  ⟨(ofBoundedDeriv f (hf.smooth.differentiable (by simp)) hf.bound hf.bound
      hf.bound_nonneg hf.bound_nonneg hf.norm_le hf.norm_fderiv_le,
    ofBoundedDeriv (fderiv ℝ f) (hf.fderiv_smooth.differentiable (by simp)) hf.bound hf.bound
      hf.bound_nonneg hf.bound_nonneg hf.norm_fderiv_le hf.norm_fderiv₂_le), by
      intro x
      exact (hf.smooth.differentiable (by simp) x).hasFDerivAt⟩

@[simp] lemma ofBoundedCThree_value {f : D → E} (hf : BoundedCThree f) (x : D) :
    cValue (ofBoundedCThree hf) x = f x := rfl

@[simp] lemma ofBoundedCThree_deriv {f : D → E} (hf : BoundedCThree f) (x : D) :
    cDeriv (ofBoundedCThree hf) x = fderiv ℝ f x := rfl

def supportedHolder (K : Set D) : Submodule ℝ (HMap D E) :=
  ⨅ x ∈ Kᶜ, ((BoundedContinuousFunction.evalCLM ℝ x).comp (valueCLM _)).ker

omit [NormedSpace ℝ D] in
lemma supportedHolder_closed (K : Set D) : IsClosed (supportedHolder (E := E) K : Set (HMap D E)) := by
  simp only [supportedHolder, Submodule.coe_iInf]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact ContinuousLinearMap.isClosed_ker _

instance (K : Set D) [CompleteSpace E] : CompleteSpace (supportedHolder (E := E) K) :=
  (supportedHolder_closed K).completeSpace_coe

omit [NormedSpace ℝ D] in
lemma mem_supportedHolder (u : HMap D E) (K : Set D) :
    u ∈ supportedHolder K ↔ ∀ x ∉ K, valueCLM _ u x = 0 := by
  simp [supportedHolder]

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
namespace HolderCompletion
variable {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance jetCoeffInst1 : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst2 : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance jetCoeffInst3 : NormedAddCommGroup (D →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst4 : NormedSpace ℝ (D →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance jetCoeffInst5 : NormedAddCommGroup (D →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst6 : NormedSpace ℝ (D →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance jetCoeffInst7 : NormedAddCommGroup (D →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance jetCoeffInst8 : NormedSpace ℝ (D →L[ℝ] E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance jetCoeffInst9 : NormedAddCommGroup (COne D E) := inferInstance
local instance jetCoeffInst10 : NormedSpace ℝ (COne D E) := inferInstance
local instance jetCoeffInst11 : NormedAddCommGroup (COne D F) := inferInstance
local instance jetCoeffInst12 : NormedSpace ℝ (COne D F) := inferInstance
local instance jetCoeffInst13 : NormedAddCommGroup (HMap D E) := inferInstance
local instance jetCoeffInst14 : NormedSpace ℝ (HMap D E) := inferInstance
local instance jetCoeffInst15 : NormedAddCommGroup (HMap D F) := inferInstance
local instance jetCoeffInst16 : NormedSpace ℝ (HMap D F) := inferInstance
local instance jetCoeffInst17 : NormedAddCommGroup (HMap D (D →L[ℝ] F)) := inferInstance
local instance jetCoeffInst18 : NormedSpace ℝ (HMap D (D →L[ℝ] F)) := inferInstance

def coefficientValueAction (M : COne D (E →L[ℝ] F)) : COne D E →L[ℝ] HMap D F :=
  (bilinCLM (X := D) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ F).flip
    (jetValueCLM _ M)).comp (jetValueCLM _)

def coefficientDerivAction (M : COne D (E →L[ℝ] F)) : COne D E →L[ℝ] HMap D (D →L[ℝ] F) :=
  (bilinCLM (X := D) (α := (1:ℝ)/3) (ContinuousLinearMap.compL ℝ D E F)
    (jetValueCLM _ M)).comp (jetDerivCLM _) +
  (bilinCLM (X := D) (α := (1:ℝ)/3)
    (ContinuousLinearMap.flipₗᵢ ℝ D E F).toContinuousLinearEquiv.toContinuousLinearMap
    (jetDerivCLM _ M)).comp (jetValueCLM _)

def coefficientAction (M : COne D (E →L[ℝ] F)) : COne D E →L[ℝ] COne D F :=
  ((coefficientValueAction M).prod (coefficientDerivAction M)).codRestrict
    (jetGraph (E := F) D ((1:ℝ)/3)) (fun u => by
      intro z
      change HasFDerivAt (fun x => cValue M x (cValue u x))
        ((cValue M z).comp (cDeriv u z)+(cDeriv M z).flip (cValue u z)) z
      exact (c_hasFDerivAt M z).clm_apply (c_hasFDerivAt u z))

@[simp] lemma coefficientAction_value (M : COne D (E →L[ℝ] F)) (u : COne D E) (z : D) :
    cValue (coefficientAction M u) z = cValue M z (cValue u z) := rfl

@[simp] lemma coefficientAction_deriv (M : COne D (E →L[ℝ] F)) (u : COne D E) (z : D) :
    cDeriv (coefficientAction M u) z =
      (cValue M z).comp (cDeriv u z)+(cDeriv M z).flip (cValue u z) := rfl

end HolderCompletion

end
section
open scoped ContDiff Topology RealInnerProductSpace
open Set Filter MeasureTheory

 def smoothCauchyKernel (δ : ℝ) (z : ℂ) : ℂ := (‖z‖^2+δ)⁻¹ • star z

 theorem smoothCauchyKernel_smooth {δ : ℝ} (hδ : 0<δ) :
    ContDiff ℝ ∞ (smoothCauchyKernel δ) := by
  exact (((contDiff_id.norm_sq ℂ).add contDiff_const).inv
    (fun z => (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ).ne')).smul
      (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff

 theorem smoothCauchyKernel_norm {δ : ℝ} (hδ : 0<δ) (z : ℂ) :
    ‖smoothCauchyKernel δ z‖ ≤ ‖z‖⁻¹ := by
  rw [smoothCauchyKernel,norm_smul,norm_star,Real.norm_of_nonneg
    (inv_nonneg.mpr (add_nonneg (sq_nonneg _) hδ.le))]
  by_cases hz : z=0
  · simp [hz]
  have hp : 0<‖z‖ := norm_pos_iff.mpr hz
  have hq : 0<‖z‖^2+δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  rw [inv_mul_eq_div,←one_div (‖z‖)]
  apply (div_le_div_iff₀ hq hp).mpr
  nlinarith

 theorem smoothCauchyKernel_fderiv {δ : ℝ} (hδ : 0<δ) (z v : ℂ) :
    fderiv ℝ (smoothCauchyKernel δ) z v =
      (‖z‖^2+δ)⁻¹ • star v -
        (2*inner ℝ z v/(‖z‖^2+δ)^2) • star z := by
  have hd := ((hasDerivAt_inv (add_pos_of_nonneg_of_pos (sq_nonneg ‖z‖) hδ).ne').comp_hasFDerivAt z
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const δ)).smul
      (starL ℝ : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  rw [show fderiv ℝ (smoothCauchyKernel δ) z = _ from hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,two_smul,smul_eq_mul,Function.comp_apply]
  change (‖z‖^2+δ)⁻¹ • star v + (-((‖z‖^2+δ)^2)⁻¹*(inner ℝ z v+inner ℝ z v)) • star z = _
  rw [sub_eq_add_neg,←neg_smul]
  congr 2
  rw [div_eq_mul_inv]
  ring

 theorem smoothCauchyKernel_fderiv_norm {δ : ℝ} (hδ : 0<δ) {z : ℂ} (hz : z≠0) (v : ℂ) :
    ‖fderiv ℝ (smoothCauchyKernel δ) z v‖ ≤ (3/‖z‖^2)*‖v‖ := by
  have hp : 0<‖z‖ := norm_pos_iff.mpr hz
  have hq : 0<‖z‖^2+δ := add_pos_of_nonneg_of_pos (sq_nonneg _) hδ
  have hib : |inner ℝ z v| ≤ ‖z‖*‖v‖ := abs_real_inner_le_norm z v
  have h1 : (‖z‖^2+δ)⁻¹ ≤ (‖z‖^2)⁻¹ := by
    exact inv_anti₀ (sq_pos_of_pos hp) (by linarith)
  have h2 : 2*|inner ℝ z v|/(‖z‖^2+δ)^2*‖z‖ ≤ (2/‖z‖^2)*‖v‖ := by
    calc
      _ ≤ (2*(‖z‖*‖v‖)/(‖z‖^2+δ)^2)*‖z‖ := by gcongr
      _ ≤ (2*(‖z‖*‖v‖)/‖z‖^4)*‖z‖ := by
        gcongr
        nlinarith [sq_nonneg δ]
      _ = _ := by field_simp
  rw [smoothCauchyKernel_fderiv hδ]
  calc
    _ ≤ ‖(‖z‖^2+δ)⁻¹ • star v‖ + ‖(2*inner ℝ z v/(‖z‖^2+δ)^2) • star z‖ := norm_sub_le _ _
    _ = (‖z‖^2+δ)⁻¹*‖v‖ + (2*|inner ℝ z v|/(‖z‖^2+δ)^2)*‖z‖ := by
      simp only [norm_smul,norm_star,Real.norm_eq_abs,abs_inv,abs_of_pos hq,
        abs_div,abs_mul,abs_pow]
      norm_num
    _ ≤ (‖z‖^2)⁻¹*‖v‖+(2/‖z‖^2)*‖v‖ :=
      add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2
    _ = _ := by ring

 theorem smoothCauchyKernel_tendsto (z : ℂ) :
    Tendsto (fun δ : ℝ => smoothCauchyKernel δ z) (𝓝[>] 0) (𝓝 z⁻¹) := by
  by_cases hz : z=0
  · simp only [hz,smoothCauchyKernel,norm_zero,zero_pow (by decide : (2:ℕ)≠0),
      zero_add,star_zero,smul_zero,inv_zero]
    exact tendsto_const_nhds
  have hn : ‖z‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hh : ContinuousAt (fun δ : ℝ => (‖z‖^2+δ)⁻¹ • star z) 0 := by
    exact (((continuous_const.add continuous_id).continuousAt.inv₀
      (by simpa only [Pi.add_apply,id_eq,add_zero] using hn)).smul continuousAt_const)
  have h := hh.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have he : (‖z‖^2)⁻¹ • star z=z⁻¹ := by
    rw [Complex.inv_def,Complex.normSq_eq_norm_sq]
    simp only [Complex.real_smul,Complex.ofReal_inv]
    exact mul_comm _ _
  simpa only [smoothCauchyKernel,add_zero,he] using h


end
section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 theorem compact_kernel_derivative_integral_zero {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) (v : ℂ) :
    (∫ w : ℂ, fderiv ℝ K w v)=0 := by
  have hi : Integrable (fun w => fderiv ℝ K w v) :=
    (((hK.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  have hi0 : Integrable (fun w : ℂ => K w) := hK.continuous.integrable_of_hasCompactSupport hc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := K) (g := fun _ : ℂ => (1:ℂ)) (v := v) (μ := volume)
    (by simpa only [mul_one] using hi) (by simp) (by simpa only [mul_one] using hi0)
    (fun w _ => hK.differentiable (by simp) w) (fun _ _ => differentiableAt_const _)
  have he : (fun x : ℂ => K x*fderiv ℝ (fun _ : ℂ => (1:ℂ)) x v)=0 := by
    funext x
    simp only [fderiv_const_apply,zero_apply,mul_zero,Pi.zero_apply]
  rw [he] at h
  change (∫ x : ℂ, (0:ℂ)) = -(∫ x : ℂ, fderiv ℝ K x v * 1) at h
  simpa only [integral_zero,mul_one,zero_eq_neg] using h

omit [CompleteSpace E] in
 theorem compact_kernel_convolution_fderiv {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      ∫ w : ℂ, fderiv ℝ K w v • g (x-w) := by
  have hd := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℂ)
    (hK.of_le (by simp)) (hg.locallyIntegrable (μ := volume)) x
  rw [hd.fderiv,convolution]
  have hi : Integrable (fun w : ℂ =>
      ((ContinuousLinearMap.lsmul ℝ ℂ).precompL ℂ) (fderiv ℝ K w) (g (x-w))) :=
    (hc.fderiv ℝ).convolutionExists_left _
      (hK.continuous_fderiv (by simp)) (hg.locallyIntegrable (μ := volume)) x
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

 theorem compact_kernel_convolution_cancel {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) (x v : ℂ) :
    fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x v =
      ∫ w : ℂ, fderiv ℝ K w v • (g (x-w)-g x) := by
  rw [compact_kernel_convolution_fderiv hK hc hg]
  have hi : Integrable (fun w : ℂ => fderiv ℝ K w v • g (x-w)) :=
    ((((hK.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const).smul
      (hg.comp (continuous_const.sub continuous_id)))).integrable_of_hasCompactSupport
        ((hc.fderiv_apply (𝕜 := ℝ) v).smul_right)
  have hi0 : Integrable (fun w : ℂ => fderiv ℝ K w v) :=
    (((hK.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v)
  simp_rw [smul_sub]
  rw [integral_sub hi (hi0.smul_const _),integral_smul_const,
    compact_kernel_derivative_integral_zero hK hc,zero_smul,sub_zero]

 theorem compact_kernel_convolution_derivative_bound {K : ℂ → ℂ}
    (hK : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) {g : ℂ → E}
    (hg : Continuous g) {W : ℂ → ℝ} (hW : Integrable W)
    (hb : ∀ x w v, ‖fderiv ℝ K w v‖*‖g (x-w)-g x‖ ≤ W w*‖v‖) (x : ℂ) :
    ‖fderiv ℝ (convolution K g (ContinuousLinearMap.lsmul ℝ ℂ) volume) x‖ ≤
      ∫ w : ℂ, W w := by
  have hW0 : 0≤ ∫ w : ℂ, W w := by
    apply integral_nonneg
    intro w
    change (0:ℝ) ≤ W w
    have h := hb 0 w 1
    simpa only [norm_one,mul_one] using (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans h
  apply ContinuousLinearMap.opNorm_le_bound _ hW0
  intro v
  rw [compact_kernel_convolution_cancel hK hc hg]
  calc
    _ ≤ ∫ w : ℂ, W w*‖v‖ := norm_integral_le_of_norm_le (hW.mul_const _)
      (Eventually.of_forall fun w => by rw [norm_smul]; exact hb x w v)
    _ = _ := integral_mul_const _ _


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
