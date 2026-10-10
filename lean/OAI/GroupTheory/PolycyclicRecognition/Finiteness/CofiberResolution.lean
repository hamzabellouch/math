import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # Exactness of the cone on an injective map of resolved representations -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]
  {A B : Rep k G} (P : ProjectiveResolution A) (Q : ProjectiveResolution B)
  (φ : P.complex ⟶ Q.complex)

theorem repCofiber_boundary_of_lift_fst (i : ℕ)
    (x : (repCofiber φ).X (i + 1))
    (hx : ((repCofiber φ).d (i + 1) i).hom x = 0)
    (a : P.complex.X (i + 1))
    (ha : (P.complex.d (i + 1) i).hom a = (repCofiberFst φ i).hom x) :
    ∃ y : (repCofiber φ).X (i + 2),
      ((repCofiber φ).d (i + 2) (i + 1)).hom y = x := by
  have hsum := repCofiber_snd_d φ i x
  rw [hx, map_zero] at hsum
  have hcycle : (Q.complex.d (i + 1) i).hom
      ((repCofiberSnd φ (i + 1)).hom x + (φ.f (i + 1)).hom a) = 0 := by
    have hc := congrArg (fun f => f.hom a) (φ.comm (i + 1) i)
    change (Q.complex.d (i + 1) i).hom ((φ.f (i + 1)).hom a) =
      (φ.f i).hom ((P.complex.d (i + 1) i).hom a) at hc
    simp only [map_add]
    rw [hc, ha]
    exact (add_comm _ _).trans hsum.symm
  obtain ⟨b, hb⟩ := (rep_shortComplex_exact_iff _).mp (Q.exact_succ i) _ hcycle
  let y := (repCofiberInl φ (i + 1)).hom (-a) +
    (repCofiberInr φ (i + 2)).hom b
  refine ⟨y, repCofiber_ext φ i ?_ ?_⟩
  · rw [repCofiber_fst_d]
    simp only [y, map_add, repCofiber_fst_inl, repCofiber_fst_inr, add_zero,
      map_neg, ha, neg_neg]
  · rw [repCofiber_snd_d]
    simp only [y, map_add, repCofiber_fst_inl, repCofiber_fst_inr,
      repCofiber_snd_inl, repCofiber_snd_inr, add_zero, map_neg, map_zero]
    rw [hb]
    abel

theorem repCofiber_boundary_of_mono (f : A ⟶ B) [Mono f]
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) (i : ℕ)
    (x : (repCofiber φ).X (i + 1))
    (hx : ((repCofiber φ).d (i + 1) i).hom x = 0) :
    ∃ y : (repCofiber φ).X (i + 2),
      ((repCofiber φ).d (i + 2) (i + 1)).hom y = x := by
  have ha : ∃ a : P.complex.X (i + 1),
      (P.complex.d (i + 1) i).hom a = (repCofiberFst φ i).hom x := by
    cases i with
    | zero =>
        have hsum := repCofiber_snd_d φ 0 x
        rw [hx, map_zero] at hsum
        have hzero : (P.π.f 0).hom ((repCofiberFst φ 0).hom x) = 0 := by
          apply ((Rep.mono_iff_injective f).mp inferInstance)
          erw [map_zero]
          have hc := congrArg (fun u => u.hom ((repCofiberFst φ 0).hom x)) hφ
          change (Q.π.f 0).hom ((φ.f 0).hom ((repCofiberFst φ 0).hom x)) =
            f.hom ((P.π.f 0).hom ((repCofiberFst φ 0).hom x)) at hc
          have hd := congrArg (fun u => u.hom ((repCofiberSnd φ 1).hom x))
            Q.complex_d_comp_π_f_zero
          change (Q.π.f 0).hom ((Q.complex.d 1 0).hom
            ((repCofiberSnd φ 1).hom x)) = 0 at hd
          rw [← hc]
          have hz := congrArg (Q.π.f 0).hom hsum.symm
          simpa only [map_add, hd, add_zero, map_zero] using! hz
        exact (rep_shortComplex_exact_iff _).mp P.exact₀ _ hzero
    | succ i =>
        have hz := repCofiber_fst_d φ i x
        rw [hx, map_zero] at hz
        have hzero := neg_eq_zero.mp hz.symm
        exact (rep_shortComplex_exact_iff _).mp (P.exact_succ i) _ hzero
  obtain ⟨a, ha⟩ := ha
  exact repCofiber_boundary_of_lift_fst P Q φ i x hx a ha

theorem repCofiber_exactAt_of_mono (f : A ⟶ B) [Mono f]
    (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) (i : ℕ) :
    (repCofiber φ).ExactAt (i + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp)]
  exact (rep_shortComplex_exact_iff _).mpr
    (repCofiber_boundary_of_mono P Q φ f hφ i)

end PolycyclicRecognition

end

end OAI
