import OAI.Geometry.HeilbronnTriangle.LatticePacking

namespace OAI


namespace Problem355.PlaneTripleCount

open Module Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem basis_from_spanning_tuple (u : Fin 3 → E)
    (hdim : Module.finrank ℝ E = 2)
    (hspan : Submodule.span ℝ (Set.range u) = ⊤) :
    ∃ b : Module.Basis (Fin 2) ℝ E, ∀ i, b i ∈ Set.range u := by
  have h := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range u)
  rw [hspan, finrank_top, hdim] at h
  obtain ⟨f, hf, hs, hlin⟩ := h
  refine ⟨Module.Basis.mk hlin hs.ge, ?_⟩
  simpa only [Module.Basis.coe_mk] using hf

variable [MeasurableSpace E] [BorelSpace E]

theorem card_spanning_triples_le (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (hdim : Module.finrank ℝ E = 2)
    (T : Finset (Fin 3 → L)) (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ u ∈ T, ∀ i, ‖(u i : E)‖ ≤ R)
    (hspan : ∀ u ∈ T,
      Submodule.span ℝ (Set.range (fun i => (u i : E))) = ⊤) :
    (T.card : ℝ) ≤ (9 * Real.pi * R ^ 2 / ZLattice.covolume L) ^ 3 := by
  classical
  by_cases hT : T.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hT
    obtain ⟨b, hb⟩ := basis_from_spanning_tuple (fun i => (u₀ i : E)) hdim (hspan u₀ hu₀)
    have hbL : ∀ i, b i ∈ L := by
      intro i
      obtain ⟨j, hj⟩ := hb i
      rw [← hj]
      exact (u₀ j).property
    have hbnorm : ∀ i, ‖b i‖ ≤ R := by
      intro i
      obtain ⟨j, hj⟩ := hb i
      rw [← hj]
      exact hnorm u₀ hu₀ j
    let A : Finset L := T.biUnion (fun u => Finset.univ.image u)
    have hmem : ∀ u ∈ T, ∀ i, u i ∈ A := by
      intro u hu i
      exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    have hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall 0 R := by
      intro a ha
      obtain ⟨u, hu, ha⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hnorm u hu i
    have hbound := LatticePacking.plane_card_le_of_short_basis L b hbL A 0 R hR hA hbnorm
    let f : {u // u ∈ T} → (Fin 3 → {a // a ∈ A}) :=
      fun u i => ⟨u.1 i, hmem u.1 u.2 i⟩
    have hf : Function.Injective f := by
      intro u v huv
      apply Subtype.ext
      funext i
      exact congrArg Subtype.val (congrFun huv i)
    have hc : T.card ≤ A.card ^ 3 := by
      have h := Fintype.card_le_of_injective f hf
      simpa using h
    have hc' : (T.card : ℝ) ≤ (A.card : ℝ) ^ 3 := by exact_mod_cast hc
    exact hc'.trans (pow_le_pow_left₀ (Nat.cast_nonneg A.card) hbound 3)
  · have hzero : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp only [hzero, Finset.card_empty, Nat.cast_zero]
    have hvol : 0 < ZLattice.covolume L := ZLattice.covolume_pos L MeasureTheory.volume
    positivity

theorem card_spanning_triples_le_index (L Γ : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (hΓ : Γ ≤ L) (hdim : Module.finrank ℝ E = 2)
    (T : Finset (Fin 3 → Γ)) (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ∀ u ∈ T, ∀ i, ‖(u i : E)‖ ≤ R)
    (hspan : ∀ u ∈ T,
      Submodule.span ℝ (Set.range (fun i => (u i : E))) = ⊤) :
    (T.card : ℝ) ≤ (9 * Real.pi) ^ 3 * R ^ 6 /
      ((Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L) ^ 3 := by
  have h := card_spanning_triples_le Γ hdim T R hR hnorm hspan
  have hLpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L MeasureTheory.volume
  have hratio := ZLattice.covolume_div_covolume_eq_relIndex' Γ L hΓ
  have hcov : ZLattice.covolume Γ =
      (Γ.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L :=
    (div_eq_iff (ne_of_gt hLpos)).mp hratio
  rw [hcov] at h
  simpa only [div_pow, mul_pow, ← pow_mul, Nat.reduceMul] using h

end Problem355.PlaneTripleCount

end OAI
