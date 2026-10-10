import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.TensorSectionSpace
import OAI.Geometry.SplitTangent.TwistedCurveTensor

namespace OAI

/-! Ambient Leaf Sections. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent

structure AmbientTransition {X : ComplexManifold.{u}} (g : RationalCurve X) (d : ℕ) where
  multiplier : ℂ × X.Carrier → ℂ
  holomorphic : ∀z : ℂ,z≠0 → ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω
    (fun x => multiplier (z,x)) (g.finite z)
  value : ∀z : ℂ,z≠0 → multiplier (z,g.finite z)=z^d

abbrev AmbientFunctionPair (X : ComplexManifold.{u}) :=
  (ℂ × X.Carrier → ℂ) × (ℂ × X.Carrier → ℂ)

def ambientSectionSpace {X : ComplexManifold.{u}} {g : RationalCurve X} {d : ℕ}
    (T : AmbientTransition g d) : Submodule ℂ (AmbientFunctionPair X) where
  carrier := {f | (∀z,ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,ℂ) ω f.1 (z,g.finite z)) ∧
    (∀z,ContMDiffAt (𝓘(ℂ,ℂ).prod (ModelWithCorners X)) 𝓘(ℂ,ℂ) ω f.2 (z,g.infinity z)) ∧
    ∀z : ℂ,z≠0 → ∀ᶠ x in 𝓝 (g.finite z),f.1 (z,x)=T.multiplier (z,x)*f.2 (z⁻¹,x)}
  zero_mem' := ⟨fun _ => contMDiffAt_const,fun _ => contMDiffAt_const,by simp⟩
  add_mem' := by
    intro f h hf hh
    refine ⟨fun z => (hf.1 z).add (hh.1 z),fun z => (hf.2.1 z).add (hh.2.1 z),?_⟩
    intro z hz
    filter_upwards [hf.2.2 z hz,hh.2.2 z hz] with x hx hy
    change f.1 (z,x)+h.1 (z,x)=T.multiplier (z,x)*(f.2 (z⁻¹,x)+h.2 (z⁻¹,x))
    rw [hx,hy,mul_add]
  smul_mem' := by
    intro c f hf
    refine ⟨fun z => (contMDiffAt_const (I' := 𝓘(ℂ,ℂ))).mul (hf.1 z),fun z => (contMDiffAt_const (I' := 𝓘(ℂ,ℂ))).mul (hf.2.1 z),?_⟩
    intro z hz
    filter_upwards [hf.2.2 z hz] with x hx
    change c * f.1 (z,x)=T.multiplier (z,x)*(c * f.2 (z⁻¹,x))
    rw [hx]
    ring

namespace AmbientTransition
variable {X : ComplexManifold.{u}} {S : TangentSplitting X} {g : RationalCurve X} {d : ℕ}
  (T : AmbientTransition g d) (A : LeafJetAtlas S)

 
def contact (m : ℕ) : Submodule ℂ (ambientSectionSpace T) where
  carrier := {f | (∀z n,n < m → A.jet (fun x => f.val.1 (z,x)) (g.finite z) n=0) ∧
    ∀z n,n < m → A.jet (fun x => f.val.2 (z,x)) (g.infinity z) n=0}
  zero_mem' := ⟨fun z n _ => A.jet_zero _ _,fun z n _ => A.jet_zero _ _⟩
  add_mem' := by
    intro f h hf hh
    constructor
    · intro z n hn
      change A.jet ((fun x => f.val.1 (z,x))+(fun x => h.val.1 (z,x))) _ _=0
      rw [A.jet_add (LeafJetAtlas.parameter_slice (f.property.1 z))
        (LeafJetAtlas.parameter_slice (h.property.1 z)),hf.1 z n hn,hh.1 z n hn,add_zero]
    · intro z n hn
      change A.jet ((fun x => f.val.2 (z,x))+(fun x => h.val.2 (z,x))) _ _=0
      rw [A.jet_add (LeafJetAtlas.parameter_slice (f.property.2.1 z))
        (LeafJetAtlas.parameter_slice (h.property.2.1 z)),hf.2 z n hn,hh.2 z n hn,add_zero]
  smul_mem' := by
    intro c f hf
    constructor
    · intro z n hn
      change A.jet (c • (fun x => f.val.1 (z,x))) _ _=0
      rw [A.jet_csmul (LeafJetAtlas.parameter_slice (f.property.1 z)),hf.1 z n hn]
      ext v
      exact mul_zero c
    · intro z n hn
      change A.jet (c • (fun x => f.val.2 (z,x))) _ _=0
      rw [A.jet_csmul (LeafJetAtlas.parameter_slice (f.property.2.1 z)),hf.2 z n hn]
      ext v
      exact mul_zero c

lemma contact_antitone : Antitone (T.contact A) := by
  intro m n hmn f hf
  exact ⟨fun z k hk => hf.1 z k (hk.trans_le hmn),fun z k hk => hf.2 z k (hk.trans_le hmn)⟩

@[simp] lemma contact_zero : T.contact A 0=⊤ := by
  ext f
  simp [contact]

 
lemma leading_overlap (m : ℕ) (f : T.contact A m) {z : ℂ} (hz : z≠0) :
    A.jet (fun x => f.val.val.1 (z,x)) (g.finite z) m =
      z^(d : ℤ) • A.jet (fun x => f.val.val.2 (z⁻¹,x)) (g.infinity z⁻¹) m := by
  have hi : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,ℂ) ω
      (fun x => f.val.val.2 (z⁻¹,x)) (g.finite z) := by
    rw [g.overlap z hz]
    exact LeafJetAtlas.parameter_slice (f.val.property.2.1 z⁻¹)
  have hzero (n : ℕ) (hn : n < m) : A.jet (fun x => f.val.val.2 (z⁻¹,x)) (g.finite z) n=0 := by
    rw [g.overlap z hz]
    exact f.property.2 _ _ hn
  calc
    _ = A.jet (fun x => T.multiplier (z,x)*f.val.val.2 (z⁻¹,x)) (g.finite z) m :=
      A.jet_congr (f.val.property.2.2 z hz) m
    _ = T.multiplier (z,g.finite z) • A.jet (fun x => f.val.val.2 (z⁻¹,x)) (g.finite z) m :=
      A.jet_smul hi (T.holomorphic z hz) m hzero
    _ = _ := by rw [T.value z hz,g.overlap z hz,zpow_natCast]

 

def leading (m : ℕ) : T.contact A m →ₗ[ℂ] symmetricSupportedTensors g S (d : ℤ) m where
  toFun f := ⟨⟨(
    fun z => A.jet (fun x => f.val.val.1 (z,x)) (g.finite z) m,
    fun z => A.jet (fun x => f.val.val.2 (z,x)) (g.infinity z) m),
    ⟨A.leading_analytic g.finite_holomorphic f.val.property.1 m f.property.1,
      A.leading_analytic g.infinity_holomorphic f.val.property.2.1 m f.property.2,
      fun z hz => T.leading_overlap A m f hz⟩⟩,
    ⟨fun z v => A.jet_supported _ _ _ v,
      fun z v => A.jet_supported _ _ _ v,
      fun z v σ => A.jet_symmetric (LeafJetAtlas.parameter_slice (f.val.property.1 z)) m v σ,
      fun z v σ => A.jet_symmetric (LeafJetAtlas.parameter_slice (f.val.property.2.1 z)) m v σ⟩⟩
  map_add' f h := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> funext z
    · exact A.jet_add (LeafJetAtlas.parameter_slice (f.val.property.1 z))
        (LeafJetAtlas.parameter_slice (h.val.property.1 z)) m
    · exact A.jet_add (LeafJetAtlas.parameter_slice (f.val.property.2.1 z))
        (LeafJetAtlas.parameter_slice (h.val.property.2.1 z)) m
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> funext z
    · exact A.jet_csmul (LeafJetAtlas.parameter_slice (f.val.property.1 z)) m c
    · exact A.jet_csmul (LeafJetAtlas.parameter_slice (f.val.property.2.1 z)) m c

lemma leading_kernel (m : ℕ) (f : T.contact A m) :
    T.leading A m f=0 ↔ f.val∈T.contact A (m+1) := by
  constructor
  · intro he
    have hh := congrArg Subtype.val (congrArg Subtype.val he)
    constructor
    · intro z n hn
      by_cases hnm : n < m
      · exact f.property.1 z n hnm
      · have hne : n=m := by omega
        subst n
        exact congrArg (fun q : (ℂ → TangentTensor X m) × (ℂ → TangentTensor X m) => q.1 z) hh
    · intro z n hn
      by_cases hnm : n < m
      · exact f.property.2 z n hnm
      · have hne : n=m := by omega
        subst n
        exact congrArg (fun q : (ℂ → TangentTensor X m) × (ℂ → TangentTensor X m) => q.2 z) hh
  · intro he
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (funext fun z => he.1 z m (Nat.lt_succ_self m))
      (funext fun z => he.2 z m (Nat.lt_succ_self m))

end AmbientTransition
end SplitTangent

end

end OAI
