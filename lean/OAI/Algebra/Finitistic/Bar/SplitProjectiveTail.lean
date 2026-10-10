import OAI.Algebra.Finitistic.Bar.ProjectiveTail

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive CategoryTheory.Category
namespace DerivedBar.ProjectiveTail
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- A local contracting identity forces exactness, without assumptions on the
first or third term. -/
theorem exact_of_local_contraction (S : ShortComplex C)
    (a : S.X₂ ⟶ S.X₁) (b : S.X₃ ⟶ S.X₂)
    (h : a ≫ S.f + S.g ≫ b = 𝟙 _) : S.Exact := by
  apply S.exact_iff_epi_toCycles.mpr
  have : IsSplitEpi S.toCycles := ⟨⟨{
    section_ := S.iCycles ≫ a
    id := by
      apply (cancel_mono S.iCycles).mp
      rw [Category.assoc, S.toCycles_i]
      have hh := congrArg (fun f => S.iCycles ≫ f) h
      simpa only [comp_add, Category.assoc, S.iCycles_g_assoc, zero_comp,
        add_zero, comp_id, id_comp] using hh }⟩⟩
  infer_instance

variable (K : ChainComplex C ℕ)

/-- Three adjacent split cycle sequences contract the middle degree. -/
theorem contraction_of_splittings (n : ℕ)
    (s0 : (cyclesSequence K n).Splitting)
    (s1 : (cyclesSequence K (n+1)).Splitting)
    (s2 : (cyclesSequence K (n+2)).Splitting) :
    (s1.r ≫ s2.s) ≫ K.d (n+3) (n+2) +
      K.d (n+2) (n+1) ≫ (s0.r ≫ s1.s) = 𝟙 (K.X (n+2)) := by
  have hleft : (s1.r ≫ s2.s) ≫ K.d (n+3) (n+2) =
      s1.r ≫ (cyclesSequence K (n+1)).f := by
    rw [← K.toCycles_i (n+3) (n+2)]
    change (s1.r ≫ s2.s) ≫ (cyclesSequence K (n+2)).g ≫
      (cyclesSequence K (n+1)).f = _
    simp only [Category.assoc, s2.s_g_assoc]
  have hright : K.d (n+2) (n+1) ≫ (s0.r ≫ s1.s) =
      (cyclesSequence K (n+1)).g ≫ s1.s := by
    rw [← K.toCycles_i (n+2) (n+1)]
    change ((cyclesSequence K (n+1)).g ≫ (cyclesSequence K n).f) ≫
      (s0.r ≫ s1.s) = _
    simp only [Category.assoc, s0.f_r_assoc]
  rw [hleft, hright]
  exact s1.id

/-- Every additive functor preserves exactness in such a split tail. -/
theorem map_exact_of_splittings (F : C ⥤ E) [F.Additive] (n : ℕ)
    (s0 : (cyclesSequence K n).Splitting)
    (s1 : (cyclesSequence K (n+1)).Splitting)
    (s2 : (cyclesSequence K (n+2)).Splitting) :
    ((F.mapHomologicalComplex (.down ℕ)).obj K).ExactAt (n+2) := by
  let L := (F.mapHomologicalComplex (.down ℕ)).obj K
  apply (L.exactAt_iff' (n+3) (n+2) (n+1) (by simp) (by simp)).mpr
  apply exact_of_local_contraction _ (F.map (s1.r ≫ s2.s)) (F.map (s0.r ≫ s1.s))
  change F.map (s1.r ≫ s2.s) ≫ F.map (K.d (n+3) (n+2)) +
    F.map (K.d (n+2) (n+1)) ≫ F.map (s0.r ≫ s1.s) = 𝟙 _
  rw [← F.map_comp, ← F.map_comp, ← F.map_add, contraction_of_splittings K n s0 s1 s2,
    F.map_id]

/-- A global dimension bound makes the exact projective tail split, uniformly
for every additive functor. The harmless two-degree allowance avoids boundary
conventions and suffices for finite cohomological amplitude. -/
theorem map_exact_tail (F : C ⥤ E) [F.Additive] (a g : ℕ)
    (he : ∀ i, a ≤ i → K.ExactAt i)
    (hp : ∀ i, Projective (K.X i))
    (hg : ∀ M : C, HasProjectiveDimensionLE M g)
    (n : ℕ) (hn : a+g+2 ≤ n) :
    ((F.mapHomologicalComplex (.down ℕ)).obj K).ExactAt n := by
  have hc (i : ℕ) (hi : a+g ≤ i) : Projective (K.cycles i) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      cycles_projective K (a+t) g (fun j hj => he j (by omega)) hp (hg _)
  let split (i : ℕ) (hi : a+g ≤ i) : (cyclesSequence K i).Splitting := by
    haveI : Projective (cyclesSequence K i).X₃ := hc i hi
    exact (cyclesSequence_shortExact K i (he i (by omega))).splittingOfProjective
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    map_exact_of_splittings K F (a+g+t)
      (split _ (by omega)) (split _ (by omega)) (split _ (by omega))
end DerivedBar.ProjectiveTail

end

end OAI
