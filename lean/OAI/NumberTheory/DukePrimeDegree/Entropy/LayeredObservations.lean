import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteLevelFutureLifts

namespace OAI

/-! # Encoding finite observations chosen by an integer height -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace DukePrimeDegree

def layeredObservation {Y : Type*} {N : ℕ → ℕ} (H : Y → ℕ)
    (P : ∀ m, Y → Fin (N m)) (x : Y) : ℕ := Nat.pair (H x) (P (H x) x).val

lemma layeredObservation_measurable {Y : Type*} [MeasurableSpace Y]
    {N : ℕ → ℕ} {H : Y → ℕ} (hH : Measurable H)
    {P : ∀ m, Y → Fin (N m)} (hP : ∀ m, Measurable (P m)) :
    Measurable (layeredObservation H P) := by
  have hvar : Measurable (fun p : ℕ × Y => (P p.1 p.2).val) :=
    measurable_from_prod_countable_right fun m =>
      (measurable_of_finite (fun u : Fin (N m) => u.val)).comp (hP m)
  exact (measurable_of_countable (fun p : ℕ × ℕ => Nat.pair p.1 p.2)).comp
    (hH.prodMk (hvar.comp (hH.prodMk measurable_id)))

lemma layeredObservation_eq {Y : Type*} {N : ℕ → ℕ} (H : Y → ℕ)
    (P : ∀ m, Y → Fin (N m)) {x y : Y}
    (h : layeredObservation H P y=layeredObservation H P x) :
    H y=H x ∧ P (H x) y=P (H x) x := by
  have hp : H y=H x ∧ (P (H y) y).val=(P (H x) x).val := Nat.pair_eq_pair.mp h
  refine ⟨hp.1,?_⟩
  apply Fin.ext
  have hv := hp.2
  rwa [hp.1] at hv

lemma layeredObservation_finite_levels {Y : Type*} {N : ℕ → ℕ}
    (H : Y → ℕ) (P : ∀ m, Y → Fin (N m)) (m : ℕ) :
    (layeredObservation H P '' {x | H x ≤ m}).Finite := by
  classical
  have hlevel (k : ℕ) : (layeredObservation H P '' {x | H x=k}).Finite := by
    apply ((Set.finite_range (fun p : Fin (N k) => Nat.pair k p.val))).subset
    rintro _ ⟨x,hx,rfl⟩
    change H x=k at hx
    subst k
    exact ⟨P (H x) x,rfl⟩
  apply (Set.Finite.biUnion (Finset.finite_toSet (Finset.range (m+1)))
    (fun k _ => hlevel k)).subset
  rintro _ ⟨x,hx,rfl⟩
  exact mem_iUnion₂.mpr ⟨H x,by simpa using Nat.lt_succ_of_le hx,
    mem_image_of_mem (layeredObservation H P) rfl⟩

lemma layeredObservation_future_eq {Y V : Type*} [TopologicalSpace V]
    {N : ℕ → ℕ} (H : Y → ℕ) (P : ∀ m, Y → Fin (N m))
    (T : Y → Y) (F : V → Y) (v₀ : V)
    (hH : ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ, H (T^[k] (F v))=H (T^[k] (F v₀)))
    (hP : ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ,
      P (H (T^[k] (F v₀))) (T^[k] (F v))=P (H (T^[k] (F v₀))) (T^[k] (F v₀))) :
    ∀ᶠ v in 𝓝 v₀, ∀ k : ℕ,
      layeredObservation H P (T^[k] (F v))=layeredObservation H P (T^[k] (F v₀)) := by
  filter_upwards [hH,hP] with v hvH hvP
  intro k
  unfold layeredObservation
  rw [hvH k,hvP k]

end DukePrimeDegree

end

end OAI
