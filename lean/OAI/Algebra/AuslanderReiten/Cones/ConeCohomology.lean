import OAI.Algebra.AuslanderReiten.Cones.ConeComparison
import OAI.Algebra.AuslanderReiten.Fibers.FiberExactness

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

private theorem cohomology_eq_iff (x y : Cocycle F G n) :
    CohomologyClass.mk x = CohomologyClass.mk y ↔
      ∃ e : Cochain F G (n - 1), δ (n - 1) n e = x.1 - y.1 := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  rfl

theorem coneComparison_injective_lift (hinj : Function.Injective (coneComparison φ n))
    (x : Cochain G G n × Cochain F F n)
    (hx : coneDiagonalDifferential n (n + 1) x = 0)
    (hc : ∃ c : Cochain F G (n - 1), coneComparisonCochain φ n x = -(δ (n - 1) n c)) :
    ∃ a : Cochain G G (n - 1) × Cochain F F (n - 1),
      coneDiagonalDifferential (n - 1) n a = x := by
  have hx₁ : δ n (n + 1) x.1 = 0 := congrArg Prod.fst hx
  have hx₂ : δ n (n + 1) x.2 = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
  let a := Cocycle.mk x.1 (n + 1) rfl hx₁
  let b := Cocycle.mk x.2 (n + 1) rfl hx₂
  have hzero : coneComparison φ n (CohomologyClass.mk a, CohomologyClass.mk b) = 0 := by
    rw [coneComparison_mk, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    obtain ⟨c, hc⟩ := hc
    refine ⟨-c, ?_⟩
    rw [δ_neg]
    exact hc.symm
  have hpair := hinj (hzero.trans (map_zero (coneComparison φ n)).symm)
  have ha : CohomologyClass.mk a = 0 := congrArg Prod.fst hpair
  have hb : CohomologyClass.mk b = 0 := congrArg Prod.snd hpair
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at ha hb
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  refine ⟨(a', -b'), ?_⟩
  ext <;> simp [coneDiagonalDifferential, ha', hb', a, b]

theorem coneComparison_surjective_lift (hsurj : Function.Surjective (coneComparison φ n))
    (c : Cochain F G n) (hc : δ n (n + 1) c = 0) :
    ∃ a : Cochain G G n × Cochain F F n,
      coneDiagonalDifferential n (n + 1) a = 0 ∧
      ∃ e : Cochain F G (n - 1), coneComparisonCochain φ n a + δ (n - 1) n e = c := by
  let z := Cocycle.mk c (n + 1) rfl hc
  obtain ⟨⟨a, b⟩, hab⟩ := hsurj (CohomologyClass.mk z)
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective b
  rw [coneComparison_mk, cohomology_eq_iff] at hab
  obtain ⟨e, he⟩ := hab
  refine ⟨(a.1, b.1), ?_, -e, ?_⟩
  · ext <;> simp [coneDiagonalDifferential]
  · rw [δ_neg, ← sub_eq_add_neg]
    rw [he]
    change coneComparisonCochain φ n (a.1, b.1) -
      (coneComparisonCochain φ n (a.1, b.1) - c) = c
    abel

variable [HasHomotopyCofiber φ]

theorem coneEnd_cocycle_is_boundary
    (hzero : ∀ m (x : Cochain G F m), x = 0)
    (hinj : Function.Injective (coneComparison φ n))
    (hsurj : Function.Surjective (coneComparison φ (n - 1)))
    (x : Cocycle (mappingCone φ) (mappingCone φ) n) :
    x ∈ coboundaries (mappingCone φ) (mappingCone φ) n := by
  let a := coneEndA φ x.1
  let b := coneEndB φ x.1
  let c := coneEndC φ x.1
  have hx : coneEnd φ a b c = x.1 := coneEnd_all_reconstruct φ hzero x.1
  have hz : δ n (n + 1) (coneEnd φ a b c) = 0 := by
    rw [hx, Cocycle.δ_eq_zero]
  obtain ⟨ha, hb, hc⟩ := (coneEnd_closed_iff φ a b c).mp hz
  have hdiag : coneDiagonalDifferential n (n + 1) (a, b) = 0 := by
    apply Prod.ext
    · exact ha
    · exact (congrArg Neg.neg hb).trans neg_zero
  have hoff : coneComparisonCochain φ n (a, b) = -(δ (n - 1) n c) := by
    apply eq_neg_iff_add_eq_zero.mpr
    change (b.comp (Cochain.ofHom φ) (add_zero n) +
      (n + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add n)) + δ (n - 1) n c = 0
    convert hc using 1
    abel
  obtain ⟨u, e, hu, he⟩ := fiber_cocycle_is_boundary
    (coneDiagonalDifferential (n - 1) n) (coneDiagonalDifferential n (n + 1))
    (-(δ_hom ℤ F G ((n - 1) - 1) (n - 1))) (-(δ_hom ℤ F G (n - 1) n))
    (coneComparisonCochain φ (n - 1)) (coneComparisonCochain φ n)
    (fun u => coneComparison_differential φ (n - 1) n (by omega) u)
    (fun u hu huc => coneComparison_injective_lift φ n hinj u hu huc)
    (by
      intro z hz
      have hz' : δ (n - 1) n z = 0 := neg_eq_zero.mp hz
      have hn : (n - 1) + 1 = n := by omega
      have hz'' : δ (n - 1) ((n - 1) + 1) z = 0 := by
        rw [hn]
        exact hz'
      obtain ⟨v, hv, w, hw⟩ := coneComparison_surjective_lift φ (n - 1) hsurj z hz''
      refine ⟨v, ?_, w, ?_⟩
      · rw [hn] at hv
        exact hv
      · simpa only [LinearMap.neg_apply, δ_hom_apply, sub_neg_eq_add] using hw)
    (a, b) c hdiag hoff
  rw [mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨coneEnd φ u.1 u.2 e, ?_⟩
  rw [← hx]
  change δ (n - 1) n (coneEnd φ u.1 u.2 e) =
    CochainComplex.mappingCone.descCochain φ
      (CochainComplex.mappingCone.liftCochain φ b c (by omega))
      (CochainComplex.mappingCone.liftCochain φ 0 a rfl) (by omega)
  apply (coneEnd_boundary_iff φ (n - 1) (by omega) u.1 u.2 e a b c).mpr
  refine ⟨congrArg Prod.fst hu, congrArg Prod.snd hu, ?_⟩
  have he' : coneComparisonCochain φ (n - 1) u + δ ((n - 1) - 1) (n - 1) e = c := by
    simpa only [LinearMap.neg_apply, δ_hom_apply, sub_neg_eq_add] using he
  change δ ((n - 1) - 1) (n - 1) e +
    u.2.comp (Cochain.ofHom φ) (add_zero (n - 1)) +
    ((n - 1) + 1).negOnePow • (Cochain.ofHom φ).comp u.1 (zero_add (n - 1)) = c
  rw [← he']
  change δ ((n - 1) - 1) (n - 1) e + _ + _ = (_ + _) + _
  abel

theorem coneEnd_cohomology_subsingleton
    (hzero : ∀ m (x : Cochain G F m), x = 0)
    (hinj : Function.Injective (coneComparison φ n))
    (hsurj : Function.Surjective (coneComparison φ (n - 1))) :
    Subsingleton (CohomologyClass (mappingCone φ) (mappingCone φ) n) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  exact (CohomologyClass.mk_eq_zero_iff x).mpr
    (coneEnd_cocycle_is_boundary φ n hzero hinj hsurj x)

theorem coneEnd_nontrivial_of_kernel
    (hzero : ∀ m (x : Cochain G F m), x = 0)
    (w : CohomologyClass G G n × CohomologyClass F F n)
    (hw : w ≠ 0) (hcomp : coneComparison φ n w = 0) :
    Nontrivial (CohomologyClass (mappingCone φ) (mappingCone φ) n) := by
  obtain ⟨a, b⟩ := w
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective b
  rw [coneComparison_mk, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)] at hcomp
  obtain ⟨c, hc⟩ := hcomp
  have hz : δ n (n + 1) (coneEnd φ a.1 b.1 (-c)) = 0 := by
    apply (coneEnd_closed_iff φ a.1 b.1 (-c)).mpr
    refine ⟨Cocycle.δ_eq_zero a _, Cocycle.δ_eq_zero b _, ?_⟩
    rw [δ_neg, hc]
    change -(b.1.comp (Cochain.ofHom φ) (add_zero n) +
      (n + 1).negOnePow • (Cochain.ofHom φ).comp a.1 (zero_add n)) + _ + _ = 0
    abel
  let z := Cocycle.mk (coneEnd φ a.1 b.1 (-c)) (n + 1) rfl hz
  have hne : CohomologyClass.mk z ≠ 0 := by
    intro heq
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at heq
    obtain ⟨y, hy⟩ := heq
    have hrecon := coneEnd_all_reconstruct φ hzero y
    rw [← hrecon] at hy
    change δ (n - 1) n (coneEnd φ (coneEndA φ y) (coneEndB φ y) (coneEndC φ y)) =
      CochainComplex.mappingCone.descCochain φ
        (CochainComplex.mappingCone.liftCochain φ b.1 (-c) (by omega))
        (CochainComplex.mappingCone.liftCochain φ 0 a.1 rfl) (by omega) at hy
    obtain ⟨ha, hb, _⟩ := (coneEnd_boundary_iff φ (n - 1) (by omega)
      (coneEndA φ y) (coneEndB φ y) (coneEndC φ y) a.1 b.1 (-c)).mp hy
    apply hw
    apply Prod.ext
    · apply (CohomologyClass.mk_eq_zero_iff a).mpr
      exact (mem_coboundaries_iff a (n - 1) (by omega)).mpr ⟨coneEndA φ y, ha⟩
    · apply (CohomologyClass.mk_eq_zero_iff b).mpr
      apply (mem_coboundaries_iff b (n - 1) (by omega)).mpr
      exact ⟨-(coneEndB φ y), by rw [δ_neg]; exact hb⟩
  exact ⟨⟨CohomologyClass.mk z, 0, hne⟩⟩

end ArExplicit

end

end OAI
