import OAI.Probability.FreeIsing.Estimates.WeightedOrbitAverage
import OAI.Probability.FreeIsing.Trees.RootedTransitivity
import OAI.Probability.FreeIsing.Trees.Shells

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367.TreeOrbitAverage

def Extension {d : ℕ} (stem : List (Fin d)) (n : ℕ) :=
  {s : List (Fin d) // s.length = n ∧ (stem ++ s).IsChain (· ≠ ·)}

instance extensionFinite {d : ℕ} (stem : List (Fin d)) (n : ℕ) :
    Finite (Extension stem n) :=
  Finite.of_injective (β := List.Vector (Fin d) n)
    (fun s : Extension stem n => (⟨s.1, s.2.1⟩ : List.Vector (Fin d) n))
    (fun _ _ h => Subtype.ext (congrArg (fun s : List.Vector (Fin d) n => s.1) h))

instance extensionFintype {d : ℕ} (stem : List (Fin d)) (n : ℕ) :
    Fintype (Extension stem n) := Fintype.ofFinite _

def extensionEquivReducedTail {d : ℕ} (stem : List (Fin d)) (c : Fin d)
    (hstem : (stem ++ [c]).IsChain (· ≠ ·)) (n : ℕ) :
    Extension (stem ++ [c]) n ≃ ReducedTail c n where
  toFun s := ⟨s.1, s.2.1, by
    have hs : (stem ++ c :: s.1).IsChain (· ≠ ·) := by
      simpa only [List.append_assoc, List.singleton_append] using s.2.2
    exact (List.isChain_split.mp hs).2⟩
  invFun s := ⟨s.1, s.2.1, by
    have hs := List.isChain_split.mpr ⟨hstem, s.2.2⟩
    simpa only [List.append_assoc, List.singleton_append] using hs⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_extension {d : ℕ} (stem : List (Fin d)) (c : Fin d)
    (hstem : (stem ++ [c]).IsChain (· ≠ ·)) (n : ℕ) :
    Fintype.card (Extension (stem ++ [c]) n) = (d - 1) ^ n := by
  rw [Fintype.card_congr (extensionEquivReducedTail stem c hstem n), card_reducedTail]

def extensionNilEquivTreeShell (d n : ℕ) :
    Extension ([] : List (Fin d)) n ≃ TreeShell d n where
  toFun s := ⟨⟨s.1, by
    change s.1.IsChain (· ≠ ·)
    exact s.2.2⟩, s.2.1⟩
  invFun s := ⟨s.1.1, s.2, by
    change s.1.1.IsChain (· ≠ ·)
    exact s.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem card_extension_nil_zero (d : ℕ) :
    Fintype.card (Extension ([] : List (Fin d)) 0) = 1 := by
  rw [Fintype.card_congr (extensionNilEquivTreeShell d 0), card_treeShell_zero]

@[simp] theorem card_extension_nil_succ (d n : ℕ) :
    Fintype.card (Extension ([] : List (Fin d)) (n + 1)) = d * (d - 1) ^ n := by
  rw [Fintype.card_congr (extensionNilEquivTreeShell d (n + 1)), card_treeShell_succ]

def endpoint {d : ℕ} {stem : List (Fin d)} {n : ℕ}
    (s : Extension stem n) : TreeVertex d := ⟨stem ++ s.1, s.2.2⟩

def FixesStemBall {d : ℕ} (stem : List (Fin d)) (g : TreeAut d) : Prop :=
  ∀ u : TreeVertex d, u.1.length ≤ stem.length → g.toEquiv u = u

theorem exists_extension_map {d : ℕ} {stem : List (Fin d)} {n : ℕ}
    (s t : Extension stem n) :
    ∃ g : TreeAut d, g.toEquiv (endpoint s) = endpoint t ∧ FixesStemBall stem g := by
  obtain ⟨g, hmap, hfix⟩ := exists_treeAut_map_common_stem n stem s.1 t.1
    s.2.1 t.2.1 s.2.2 t.2.2
  exact ⟨g, Subtype.ext hmap, hfix⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_weight_mul_extension_average
    {d : ℕ} {stem : List (Fin d)} {n : ℕ} (s₀ : Extension stem n)
    (act : TreeAut d → Ω ≃ᵐ Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (weight : Ω → ℝ) (F : TreeVertex d → Ω → ℝ)
    (hw : ∀ g, FixesStemBall stem g → ∀ᵐ ω ∂μ, weight (act g ω) = weight ω)
    (hcov : ∀ g, FixesStemBall stem g → ∀ v, ∀ᵐ ω ∂μ,
      F v (act g ω) = F (g.toEquiv v) ω)
    (hF : Integrable (fun ω => weight ω * F (endpoint s₀) ω) μ) :
    (∫ ω, weight ω * F (endpoint s₀) ω ∂μ) =
      ∫ ω, weight ω * WeightedOrbitAverage.average
        (fun s : Extension stem n => F (endpoint s)) ω ∂μ := by
  classical
  let : Nonempty (Extension stem n) := ⟨s₀⟩
  choose g hg hfix using fun s : Extension stem n => exists_extension_map s₀ s
  have hcov' : ∀ s : Extension stem n, ∀ᵐ ω ∂μ,
      F (endpoint s₀) (act (g s) ω) = F (endpoint s) ω := by
    intro s
    simpa only [hg s] using hcov (g s) (hfix s) (endpoint s₀)
  calc
    (∫ ω, weight ω * F (endpoint s₀) ω ∂μ) =
        ∫ ω, weight ω * WeightedOrbitAverage.average
          (fun s : Extension stem n => fun ω => F (endpoint s₀) (act (g s) ω)) ω ∂μ :=
      (WeightedOrbitAverage.integral_weight_mul_orbit_average
        (fun s => act (g s)) (fun s => hact (g s)) weight (F (endpoint s₀))
        (fun s => hw (g s) (hfix s)) hF).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hcov'] with ω hω
      congr 1
      unfold WeightedOrbitAverage.average
      congr 1
      exact Finset.sum_congr rfl (fun s _ => hω s)

theorem integral_weight_mul_le_extension_average
    {d : ℕ} {stem : List (Fin d)} {n : ℕ} (s₀ : Extension stem n)
    (act : TreeAut d → Ω ≃ᵐ Ω) (hact : ∀ g, MeasurePreserving (act g) μ μ)
    (weight : Ω → ℝ) (F : TreeVertex d → Ω → ℝ)
    (G : Extension stem n → Ω → ℝ)
    (hw : ∀ g, FixesStemBall stem g → ∀ᵐ ω ∂μ, weight (act g ω) = weight ω)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ weight ω)
    (hcov : ∀ g, FixesStemBall stem g → ∀ v, ∀ᵐ ω ∂μ,
      F v (act g ω) = F (g.toEquiv v) ω)
    (hF : Integrable (fun ω => weight ω * F (endpoint s₀) ω) μ)
    (hG : ∀ s, Integrable (fun ω => weight ω * G s ω) μ)
    (hFG : ∀ s, ∀ᵐ ω ∂μ, F (endpoint s) ω ≤ G s ω) :
    (∫ ω, weight ω * F (endpoint s₀) ω ∂μ) ≤
      ∫ ω, weight ω * WeightedOrbitAverage.average G ω ∂μ := by
  classical
  let : Nonempty (Extension stem n) := ⟨s₀⟩
  choose g hg hfix using fun s : Extension stem n => exists_extension_map s₀ s
  apply WeightedOrbitAverage.integral_weight_mul_le_average
    (fun s => act (g s)) (fun s => hact (g s)) weight (F (endpoint s₀)) G
    (fun s => hw (g s) (hfix s)) hw0 hF hG
  intro s
  filter_upwards [hcov (g s) (hfix s) (endpoint s₀), hFG s] with ω hω hbound
  rw [hg s] at hω
  exact hω.trans_le hbound

end Problem367.TreeOrbitAverage

end

end OAI
