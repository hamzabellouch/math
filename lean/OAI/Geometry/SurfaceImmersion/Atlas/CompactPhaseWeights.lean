import OAI.Geometry.Immersion.ClosedSurface.PhaseWeights

namespace OAI

/-! Positive frequency weights giving good sums and differences on the
actual compact pairwise phase supports. -/
noncomputable section
open Set

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

theorem finite_set_compact_good_weights {ι X : Type*} [TopologicalSpace X] {n : ℕ}
    (K : ι → ι → Set X) (hK : ∀ a b, IsCompact (K a b))
    (hKs : ∀ a b, K a b = K b a)
    (B : X → Fin 3 → RVec n) (ξ : ι → X → Base)
    (hB : Continuous B) (hξ : ∀ a, Continuous (ξ a))
    (hgood : ∀ a b, a ≠ b → ∀ x ∈ K a b, Good (B x) (ξ a x))
    (s : Finset ι) :
    ∃ w : ι → ℝ, (∀ a ∈ s, 0 < w a) ∧
      ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∀ x ∈ K a b,
        Good (B x) (w a • ξ a x + w b • ξ b x) ∧
        Good (B x) (w a • ξ a x - w b • ξ b x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ => 1, ?_, ?_⟩ <;> simp
  | @insert a s ha ih =>
      obtain ⟨w, hw, hpairs⟩ := ih
      let : ∀ b : {b // b ∈ s}, CompactSpace (K a b.1) :=
        fun b => isCompact_iff_compactSpace.mp (hK a b.1)
      obtain ⟨lam, hlam, hdominant⟩ := exists_dominant_weight
        (ι := {b // b ∈ s}) (X := fun b => K a b.1)
        (fun _ x => B x.1) (fun _ x => ξ a x.1) (fun b x => ξ b.1 x.1)
        (fun _ => hB.comp continuous_subtype_val)
        (fun _ => (hξ a).comp continuous_subtype_val)
        (fun b => (hξ b.1).comp continuous_subtype_val)
        (fun b x => hgood a b.1 (fun hab => ha (hab.symm ▸ b.2)) x.1 x.2)
        (fun b => w b.1)
      let w' := Function.update w a lam
      have hw'a : w' a = lam := Function.update_self a lam w
      have hw'old (b : ι) (hb : b ∈ s) : w' b = w b := by
        exact Function.update_of_ne (fun hba : b = a => ha (hba ▸ hb)) lam w
      refine ⟨w', ?_, ?_⟩
      · intro b hb
        rcases Finset.mem_insert.mp hb with hba | hb
        · rw [hba,hw'a]
          exact hlam
        · rw [hw'old b hb]
          exact hw b hb
      · intro b hb c hc hbc x hx
        rcases Finset.mem_insert.mp hb with hba | hb
        · subst b
          have hc' : c ∈ s := (Finset.mem_insert.mp hc).resolve_left hbc.symm
          rw [hw'a, hw'old c hc']
          exact hdominant ⟨c,hc'⟩ ⟨x,hx⟩
        · rcases Finset.mem_insert.mp hc with hca | hc
          · subst c
            have hxa : x ∈ K a b := by rwa [hKs a b]
            have hh := hdominant ⟨b,hb⟩ ⟨x,hxa⟩
            rw [hw'old b hb, hw'a]
            refine ⟨?_, ?_⟩
            · simpa only [add_comm] using hh.1
            · simpa only [neg_sub] using good_neg hh.2
          · rw [hw'old b hb, hw'old c hc]
            exact hpairs b hb c hc hbc x hx

/-- One fixed positive weight for each member of an arbitrary finite
phase family makes all distinct pairwise sums and differences good on
their prescribed symmetric compact supports. -/
theorem finite_compact_good_weights {ι X : Type*} [Finite ι] [TopologicalSpace X] {n : ℕ}
    (K : ι → ι → Set X) (hK : ∀ a b, IsCompact (K a b))
    (hKs : ∀ a b, K a b = K b a)
    (B : X → Fin 3 → RVec n) (ξ : ι → X → Base)
    (hB : Continuous B) (hξ : ∀ a, Continuous (ξ a))
    (hgood : ∀ a b, a ≠ b → ∀ x ∈ K a b, Good (B x) (ξ a x)) :
    ∃ w : ι → ℝ, (∀ a, 0 < w a) ∧
      ∀ a b, a ≠ b → ∀ x ∈ K a b,
        Good (B x) (w a • ξ a x + w b • ξ b x) ∧
        Good (B x) (w a • ξ a x - w b • ξ b x) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨w,hw,hpairs⟩ := finite_set_compact_good_weights K hK hKs B ξ hB hξ hgood
    (Finset.univ : Finset ι)
  exact ⟨w,fun a => hw a (Finset.mem_univ a),
    fun a b => hpairs a (Finset.mem_univ a) b (Finset.mem_univ b)⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
