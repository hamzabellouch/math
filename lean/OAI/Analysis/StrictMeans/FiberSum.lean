import OAI.Analysis.StrictMeans.PairingCovariance

namespace OAI

section
open Set MeasureTheory
open scoped ENNReal
namespace StrictInverseFirstPower
noncomputable section

def fiberSum {X Y : Type*} (G : X → Y) (s : Set X) (h : X → ℝ≥0∞) (ξ : Y) : ℝ≥0∞ :=
  ∑' z : {z | z ∈ s ∧ G z = ξ}, h z

lemma fiberSum_le_of_injection {X Y : Type*} {G : X → Y} {s t : Set X}
    {h q : X → ℝ≥0∞} (R : s → X) (hR : Function.Injective R)
    (hRt : ∀ z, R z ∈ t) (hG : ∀ z, G (R z) = G z)
    (hw : ∀ z : s, h z ≤ q (R z)) (ξ : Y) :
    fiberSum G s h ξ ≤ fiberSum G t q ξ := by
  let r : {z | z ∈ s ∧ G z = ξ} → {z | z ∈ t ∧ G z = ξ} :=
    fun z => ⟨R ⟨z.1,z.2.1⟩,hRt _,(hG _).trans z.2.2⟩
  have hr : Function.Injective r := by
    intro z w he
    apply Subtype.ext
    have e : (⟨z.val,z.property.1⟩ : s) = ⟨w.val,w.property.1⟩ :=
      hR (congrArg Subtype.val he)
    exact congrArg (fun a : s => (a : X)) e
  exact Summable.tsum_le_tsum_of_inj r hr (fun _ _ => bot_le) (fun z => hw ⟨z.1,z.2.1⟩)
    ENNReal.summable ENNReal.summable

lemma fiberSum_iUnion {X Y I : Type*} (G : X → Y) (s : I → Set X) (h : X → ℝ≥0∞)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (ξ : Y) :
    fiberSum G (⋃ i, s i) h ξ = ∑' i, fiberSum G (s i) h ξ := by
  unfold fiberSum
  have he : {z | z ∈ ⋃ i, s i ∧ G z = ξ} = ⋃ i, {z | z ∈ s i ∧ G z = ξ} := by
    ext z
    simp only [mem_ofPred_eq,mem_iUnion]
    tauto
  rw [he]
  apply ENNReal.tsum_biUnion
  intro i _ j _ hij
  exact (hd hij).mono (fun _ hz => hz.1) (fun _ hz => hz.1)

lemma fiberSum_eq_single {X Y : Type*} {G : X → Y} {s : Set X} {h : X → ℝ≥0∞}
    (hi : InjOn G s) {z : X} (hz : z ∈ s) : fiberSum G s h (G z) = h z := by
  unfold fiberSum
  apply tsum_eq_single (⟨z,hz,rfl⟩ : {w | w ∈ s ∧ G w = G z})
  intro w hw
  exact False.elim (hw (Subtype.ext (hi w.2.1 hz w.2.2)))

lemma fiberSum_eq_zero_of_not_mem_image {X Y : Type*} {G : X → Y} {s : Set X}
    {h : X → ℝ≥0∞} {ξ : Y} (hξ : ξ ∉ G '' s) : fiberSum G s h ξ = 0 := by
  have : IsEmpty {z | z ∈ s ∧ G z = ξ} := ⟨fun z => hξ ⟨z,z.2.1,z.2.2⟩⟩
  simp [fiberSum]

lemma fiberSum_eq_indicator_inverse {X Y : Type*} {G : X → Y} {s : Set X}
    (hi : InjOn G s) (h : X → ℝ≥0∞) (φ : Y → X) (hφ : ∀ z ∈ s, φ (G z) = z) :
    fiberSum G s h = (G '' s).indicator (fun ξ => h (φ ξ)) := by
  classical
  funext ξ
  by_cases hξ : ξ ∈ G '' s
  · obtain ⟨z,hz,rfl⟩ := hξ
    rw [fiberSum_eq_single hi hz,indicator_of_mem (mem_image_of_mem G hz),hφ z hz]
  · rw [fiberSum_eq_zero_of_not_mem_image hξ,indicator_of_notMem hξ]

end
end StrictInverseFirstPower

end

end OAI
