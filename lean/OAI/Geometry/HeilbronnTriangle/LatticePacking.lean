import Mathlib

namespace OAI


open MeasureTheory MeasureTheory.Measure Set
open scoped Pointwise ENNReal

namespace Problem355.LatticePacking

theorem card_mul_measure_le {G E : Type*} [AddGroup G]
    [MeasurableSpace G] [MeasurableSpace E] [AddAction G E]
    [MeasurableVAdd G E] (μ : Measure E) [VAddInvariantMeasure G E μ]
    {F T : Set E} (hF : IsAddFundamentalDomain G F μ)
    (A : Finset G) (hAT : ∀ a ∈ A, a +ᵥ F ⊆ T) :
    (A.card : ℝ≥0∞) * μ F ≤ μ T := by
  calc
    (A.card : ℝ≥0∞) * μ F = ∑ a ∈ A, μ (a +ᵥ F) := by
      simp [measure_vadd, nsmul_eq_mul]
    _ = μ (⋃ a ∈ A, a +ᵥ F) := by
      symm
      exact measure_biUnion_finset₀
        (fun a _ b _ hab => hF.aedisjoint hab)
        (fun a _ => hF.nullMeasurableSet.vadd a)
    _ ≤ μ T := measure_mono (iUnion_subset fun a => iUnion_subset (hAT a))

theorem card_mul_measure_le_closedBall {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    (L : AddSubgroup E) {F : Set E} (hF : IsAddFundamentalDomain L F μ)
    (A : Finset L) (c : E) (R D : ℝ)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hFD : F ⊆ Metric.closedBall 0 D) :
    (A.card : ℝ≥0∞) * μ F ≤ μ (Metric.closedBall c (R + D)) := by
  apply card_mul_measure_le μ hF A
  intro a ha y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have ha' : ‖(a : E) - c‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hA a ha
  have hx' : ‖x‖ ≤ D := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hFD hx
  change dist ((a : E) + x) c ≤ R + D
  rw [dist_eq_norm, show (a : E) + x - c = ((a : E) - c) + x by abel]
  exact (norm_add_le _ _).trans (add_le_add ha' hx')

theorem fundamentalDomain_subset_closedBall {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (b : Module.Basis ι ℝ E) :
    ZSpan.fundamentalDomain b ⊆ Metric.closedBall 0 (∑ i, ‖b i‖) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  calc
    ‖x‖ = ‖∑ i, b.repr x i • b i‖ := congrArg norm (b.sum_repr x).symm
    _ ≤ ∑ i, ‖b.repr x i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖b i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hx i).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hx i).2.le

theorem card_mul_measure_le_basis {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] (μ : Measure E) [IsAddHaarMeasure μ]
    (b : Module.Basis ι ℝ E)
    (A : Finset (Submodule.span ℤ (Set.range b))) (c : E) (R : ℝ)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R) :
    (A.card : ℝ≥0∞) * μ (ZSpan.fundamentalDomain b) ≤
      μ (Metric.closedBall c (R + ∑ i, ‖b i‖)) := by
  exact card_mul_measure_le_closedBall μ
    (Submodule.span ℤ (Set.range b)).toAddSubgroup
    (ZSpan.isAddFundamentalDomain' b μ) A c R _ hA
    (fundamentalDomain_subset_closedBall b)

theorem plane_card_mul_area_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : Module.Basis (Fin 2) ℝ E)
    (A : Finset (Submodule.span ℤ (Set.range b)))
    (c : E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hb : ∀ i, ‖b i‖ ≤ R) :
    (A.card : ℝ) * volume.real (ZSpan.fundamentalDomain b) ≤
      9 * Real.pi * R ^ 2 := by
  have hFD : ZSpan.fundamentalDomain b ⊆ Metric.closedBall 0 (2 * R) := by
    refine (fundamentalDomain_subset_closedBall b).trans (Metric.closedBall_subset_closedBall ?_)
    simpa [Fin.sum_univ_two, two_mul] using add_le_add (hb 0) (hb 1)
  have h := card_mul_measure_le_closedBall volume
    (Submodule.span ℤ (Set.range b)).toAddSubgroup
    (ZSpan.isAddFundamentalDomain' b volume) A c R (2 * R) hA hFD
  have hdim : Module.finrank ℝ E = 2 := by
    rw [Module.finrank_eq_card_basis b]
    simp
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hvol : volume (Metric.closedBall c (R + 2 * R)) =
      ENNReal.ofReal (R + 2 * R) ^ 2 * ENNReal.ofReal Real.pi := by
    simpa [hdim] using InnerProductSpace.volume_closedBall_of_dim_even
      (k := 1) (by simpa using hdim) c (R + 2 * R)
  rw [hvol] at h
  have h' := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ R + 2 * R),
    ENNReal.toReal_ofReal Real.pi_pos.le] at h'
  change (A.card : ℝ) * (volume (ZSpan.fundamentalDomain b)).toReal ≤ _
  nlinarith [h']

theorem card_le_relIndex_mul {E : Type*} [NormedAddCommGroup E]
    (H L : AddSubgroup E) [Finite (L ⧸ H.addSubgroupOf L)]
    (A : Finset L) (c : E) (R C : ℝ)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hH : ∀ (B : Finset H) (d : E),
      (∀ b ∈ B, (b : E) ∈ Metric.closedBall d R) → (B.card : ℝ) ≤ C) :
    (A.card : ℝ) ≤ (H.relIndex L : ℝ) * C := by
  classical
  let Q := L ⧸ H.addSubgroupOf L
  let : Fintype Q := Fintype.ofFinite Q
  let f : L → Q := QuotientAddGroup.mk
  have hfiber (q : Q) : ((A.filter fun a => f a = q).card : ℝ) ≤ C := by
    let S := A.filter fun a => f a = q
    have hmem (a : L) (ha : a ∈ S) : (a - q.out : L) ∈ H.addSubgroupOf L := by
      apply QuotientAddGroup.eq_iff_sub_mem.mp
      exact (Finset.mem_filter.mp ha).2.trans (Quotient.out_eq q).symm
    let shift : {a // a ∈ S} → H := fun a =>
      ⟨(a.1 : E) - (q.out : E), hmem a.1 a.2⟩
    have hinj : Function.Injective shift := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      simpa only [shift, sub_left_inj] using (congrArg Subtype.val hab)
    let B := S.attach.image shift
    have hcard : B.card = S.card :=
      (Finset.card_image_of_injective _ hinj).trans Finset.card_attach
    rw [← hcard]
    apply hH B (c - (q.out : E))
    intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    change dist ((a.1 : E) - (q.out : E)) (c - (q.out : E)) ≤ R
    simpa only [dist_sub_right, Metric.mem_closedBall] using hA a.1 (Finset.mem_filter.mp a.2).1
  have hdecomp : A.card = ∑ q : Q, (A.filter fun a => f a = q).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  calc
    (A.card : ℝ) = ∑ q : Q, ((A.filter fun a => f a = q).card : ℝ) := by
      rw [hdecomp, Nat.cast_sum]
    _ ≤ ∑ _q : Q, C := Finset.sum_le_sum (fun q _ => hfiber q)
    _ = (H.relIndex L : ℝ) * C := by
      simp [AddSubgroup.relIndex, AddSubgroup.index, Q, Nat.card_eq_fintype_card,
        nsmul_eq_mul]

theorem plane_card_le_of_short_basis {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin 2) ℝ E)
    (hbL : ∀ i, b i ∈ L)
    (A : Finset L) (c : E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hb : ∀ i, ‖b i‖ ≤ R) :
    (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
  let H := Submodule.span ℤ (Set.range b)
  have hHL : H ≤ L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hbL i
  have hHpos : 0 < ZLattice.covolume H := ZLattice.covolume_pos H volume
  have hLpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  have hratio := ZLattice.covolume_div_covolume_eq_relIndex' H L hHL
  have hindex : H.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    intro hz
    rw [hz, Nat.cast_zero] at hratio
    exact (ne_of_gt (div_pos hHpos hLpos)) hratio
  let : Finite (L.toAddSubgroup ⧸ H.toAddSubgroup.addSubgroupOf L.toAddSubgroup) :=
    AddSubgroup.index_ne_zero_iff_finite.mp hindex
  have hbound : (A.card : ℝ) ≤
      (H.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) *
        (9 * Real.pi * R ^ 2 / ZLattice.covolume H) := by
    apply card_le_relIndex_mul H.toAddSubgroup L.toAddSubgroup A c R _ hA
    intro B d hB
    apply (le_div_iff₀ hHpos).mpr
    have h := plane_card_mul_area_le b B d R hR hB hb
    have hvol : ZLattice.covolume H = volume.real (ZSpan.fundamentalDomain b) :=
      ZLattice.covolume_eq_measure_fundamentalDomain H volume
        (ZSpan.isAddFundamentalDomain b volume)
    rwa [hvol]
  exact calc
    (A.card : ℝ) ≤ (H.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) *
        (9 * Real.pi * R ^ 2 / ZLattice.covolume H) := hbound
    _ = 9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
      rw [← hratio]
      field_simp

theorem plane_card_le_of_short_independent {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : Fin 2 → E) (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L)
    (A : Finset L) (c : E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, (a : E) ∈ Metric.closedBall c R)
    (hvn : ∀ i, ‖v i‖ ≤ R) :
    (A.card : ℝ) ≤ 9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
  let b := basisOfLinearIndependentOfCardEqFinrank hv (by simpa using hdim.symm)
  apply plane_card_le_of_short_basis L b (by simpa [b] using hvL) A c R hR hA
  simpa [b] using hvn

theorem card_tuples_le_pow {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Finset (Fin m → α)) (C : ℝ)
    (hA : ∀ i, ((A.image (fun a => a i)).card : ℝ) ≤ C) :
    (A.card : ℝ) ≤ C ^ m := by
  classical
  let B : Fin m → Finset α := fun i => A.image (fun a => a i)
  have hsub : A ⊆ Fintype.piFinset B := by
    intro a ha
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hcard : A.card ≤ ∏ i, (B i).card := by
    simpa only [Fintype.card_piFinset] using Finset.card_le_card hsub
  exact calc
    (A.card : ℝ) ≤ ∏ i, ((B i).card : ℝ) := by
      simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ)).mpr hcard
    _ ≤ ∏ _i : Fin m, C :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hA i)
    _ = C ^ m := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem plane_spanning_triples_card_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Finset (Fin 3 → L)) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ R)
    (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)]) :
    (A.card : ℝ) ≤ (9 * Real.pi * R ^ 2 / ZLattice.covolume L) ^ 3 := by
  classical
  by_cases hne : A.Nonempty
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨i, j, hij⟩ := hpair a ha
    let v : Fin 2 → E := ![(a i : E), (a j : E)]
    have hvL : ∀ k, v k ∈ L := by
      intro k
      fin_cases k <;> exact Subtype.coe_prop _
    have hvn : ∀ k, ‖v k‖ ≤ R := by
      intro k
      fin_cases k
      · exact hA a ha i
      · exact hA a ha j
    let B : Fin 3 → Finset L := fun k => A.image (fun t => t k)
    have hB (k : Fin 3) : ((B k).card : ℝ) ≤
        9 * Real.pi * R ^ 2 / ZLattice.covolume L := by
      apply plane_card_le_of_short_independent hdim L v hij hvL (B k) 0 R hR _ hvn
      intro u hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hA t ht k
    exact card_tuples_le_pow A _ hB
  · have hzero : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst A
    simp only [Finset.card_empty, Nat.cast_zero]
    exact pow_nonneg (div_nonneg (by positivity) (ZLattice.covolume_pos L volume).le) 3

theorem affine_plane_card_le {P E : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
    [MeasurableSpace P] [BorelSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : P →ₗᵢ[ℝ] E) (hdim : Module.finrank ℝ P = 2)
    (L : Submodule ℤ P) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : Fin 2 → P) (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ L)
    (A : Finset E) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, ‖a‖ ≤ R) (hvn : ∀ i, ‖v i‖ ≤ R)
    (hdiff : ∀ a ∈ A, ∀ b ∈ A, ∃ u : L, e (u : P) = a - b) :
    (A.card : ℝ) ≤ 36 * Real.pi * R ^ 2 / ZLattice.covolume L := by
  classical
  rcases A.eq_empty_or_nonempty with hzero | ⟨a0, ha0⟩
  · subst A
    simp only [Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (by positivity) (ZLattice.covolume_pos L volume).le
  choose u hu using fun a : {a // a ∈ A} => hdiff a.1 a.2 a0 ha0
  have hinj : Function.Injective u := by
    intro a b hab
    have h := congrArg (fun w : L => e (w : P)) hab
    rw [hu a, hu b] at h
    exact Subtype.ext (sub_left_inj.mp h)
  let B : Finset L := A.attach.image u
  have hcard : B.card = A.card :=
    (Finset.card_image_of_injective _ hinj).trans Finset.card_attach
  have hB : ∀ b ∈ B, (b : P) ∈ Metric.closedBall 0 (2 * R) := by
    intro b hb
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, ← e.norm_map (u a : P), hu a]
    exact (norm_sub_le _ _).trans (by linarith [hA a.1 a.2, hA a0 ha0])
  have hvn' : ∀ i, ‖v i‖ ≤ 2 * R := fun i => (hvn i).trans (by linarith)
  have hbound := plane_card_le_of_short_independent hdim L v hv hvL B 0 (2 * R)
    (by positivity) hB hvn'
  exact calc
    (A.card : ℝ) = (B.card : ℝ) := by rw [hcard]
    _ ≤ 9 * Real.pi * (2 * R) ^ 2 / ZLattice.covolume L := hbound
    _ = 36 * Real.pi * R ^ 2 / ZLattice.covolume L := by ring

theorem kernel_fiber_card_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) (f : E →ₗ[ℝ] ℝ)
    (hdim : Module.finrank ℝ f.ker = 2)
    [DiscreteTopology (ZLattice.comap ℝ Λ f.ker.subtype)]
    [IsZLattice ℝ (ZLattice.comap ℝ Λ f.ker.subtype)]
    (v : Fin 2 → f.ker) (hv : LinearIndependent ℝ v)
    (hvΛ : ∀ i, (v i : E) ∈ Λ)
    (A : Finset E) (R c : ℝ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, ‖a‖ ≤ R) (hvn : ∀ i, ‖v i‖ ≤ R)
    (hΛ : ∀ a ∈ A, a ∈ Λ) (hf : ∀ a ∈ A, f a = c) :
    (A.card : ℝ) ≤ 36 * Real.pi * R ^ 2 /
      ZLattice.covolume (ZLattice.comap ℝ Λ f.ker.subtype) := by
  apply affine_plane_card_le f.ker.subtypeₗᵢ hdim
    (ZLattice.comap ℝ Λ f.ker.subtype) v hv hvΛ A R hR hA hvn
  intro a ha b hb
  have hab : a - b ∈ f.ker := by
    rw [LinearMap.mem_ker, map_sub, hf a ha, hf b hb, sub_self]
  exact ⟨⟨⟨a - b, hab⟩, Λ.sub_mem (hΛ a ha) (hΛ b hb)⟩, rfl⟩

end Problem355.LatticePacking

end OAI
