import OAI.Analysis.AncientFlat.Kernel.SymbolSemigroup
import OAI.Analysis.AncientFlat.Evolution.MovingSymmetry

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma preserves_of_unit (S : ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)))
    (h0 : S 0=ContinuousLinearMap.id ℂ C₀(V,ℂ))
    (ha : ∀ s t : ℝ, 0 ≤ s → 0≤t → S (s+t)=(S t).comp (S s))
    (P : C₀(V,ℂ) → Prop)
    (hunit : ∀ t ∈ Icc (0:ℝ) 1, ∀ d, P d → P (S t d)) :
    ∀ t : ℝ, 0≤t → ∀ d, P d → P (S t d) := by
  have hn (n : ℕ) : ∀ d, P d → P (S (n:ℝ) d) := by
    induction n with
    | zero => simpa only [Nat.cast_zero,h0,ContinuousLinearMap.id_apply] using (fun d (hd : P d) => hd)
    | succ n ih =>
      intro d hd
      rw [Nat.cast_succ,ha n 1 (Nat.cast_nonneg n) zero_le_one,ContinuousLinearMap.comp_apply]
      exact hunit 1 ⟨zero_le_one,le_rfl⟩ _ (ih d hd)
  intro t ht d hd
  let n := ⌊t⌋₊
  let r : ℝ := t-n
  have hr : r ∈ Icc (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr (Nat.floor_le ht),by dsimp [r,n]; linarith [Nat.lt_floor_add_one t]⟩
  have he : t=(n:ℝ)+r := by dsimp [r]; ring
  rw [he,ha n r (Nat.cast_nonneg n) hr.1,ContinuousLinearMap.comp_apply]
  exact hunit r hr _ (hn n d hd)
theorem exists_radial_real_semigroup (c : ℝ) (Af Bf : V → ℝ)
    (h : SymbolBounds c Af Bf) (hAf : Radial Af) (hBf : Radial Bf) :
    ∃ K : ℝ, 0≤K ∧ ∃ S : ℝ → (C₀(V,ℂ) →L[ℂ] C₀(V,ℂ)),
      S 0=ContinuousLinearMap.id ℂ C₀(V,ℂ) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ‖S t‖≤K) ∧
      (∀ d : C₀(V,ℂ), ContinuousOn (fun t => S t d) (Ici (0:ℝ))) ∧
      (∀ s t : ℝ, 0 ≤ s → 0≤t → S (s+t)=(S t).comp (S s)) ∧
      (∀ d : C₀(V,ℂ), ∃ u : ℝ → C₀(V,ℂ), MovesClassically Af Bf d u ∧
        ∀ t ∈ Icc (0:ℝ) 1, ∀ x, S t d x=u t (Real.exp (-t/4) • x)) ∧
      (∀ t : ℝ, 0≤t → ∀ d : C₀(V,ℂ), Radial (d : V → ℂ) → Radial (S t d : V → ℂ)) ∧
      (∀ t : ℝ, 0≤t → ∀ d : C₀(V,ℂ), RealValued (d : V → ℂ) → RealValued (S t d : V → ℂ)) := by
  obtain ⟨K,hK,S,h0,hbound,hcont,hadd,hE⟩ := exists_symbol_semigroup c Af Bf h
  refine ⟨K,hK,S,h0,hbound,hcont,hadd,hE,?_,?_⟩
  · apply preserves_of_unit S h0 hadd (fun d => Radial (d : V → ℂ))
    intro t ht d hd
    obtain ⟨u,hu,he⟩ := hE d
    intro R x
    rw [he t ht,he t ht,←R.map_smul]
    exact hu.radial h hAf hBf hd t ht R _
  · apply preserves_of_unit S h0 hadd (fun d => RealValued (d : V → ℂ))
    intro t ht d hd
    obtain ⟨u,hu,he⟩ := hE d
    intro x
    rw [he t ht]
    exact hu.realValued h hd t ht _
end FlatSimilarity

end

end OAI
