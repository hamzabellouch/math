import OAI.Analysis.TracialSplitting.OrthogonalElements

namespace OAI

noncomputable section

universe uA uι

open Filter Topology

namespace Pureness

section

open Filter Topology

variable {A : Type uA} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem cstar_cuntzSubequiv_refl (a : A) : CuntzSubequiv a a := by
  apply (cuntzSubequiv_iff_norm a a).mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  let l := CStarAlgebra.approximateUnit A
  have hu := CStarAlgebra.increasingApproximateUnit A
  have hleft : ∀ᶠ e in l, ‖a - a * e‖ < ε / 2 := by
    have h := (hu.tendsto_mul_left a).eventually (Metric.ball_mem_nhds a hε2)
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using h
  have hright : ∀ᶠ e in l, ‖a - e * a‖ < ε / 2 := by
    have h := (hu.tendsto_mul_right a).eventually (Metric.ball_mem_nhds a hε2)
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using h
  obtain ⟨e, he1, he2, hen, hestar⟩ :=
    (hleft.and (hright.and (hu.eventually_norm.and hu.eventually_star_eq))).exists
  refine ⟨e, ?_⟩
  have heq : a - star e * a * e = (a - a * e) + (a - e * a) * e := by
    rw [hestar]
    noncomm_ring
  calc
    ‖a - star e * a * e‖ = ‖(a - a * e) + (a - e * a) * e‖ := by rw [heq]
    _ ≤ ‖a - a * e‖ + ‖(a - e * a) * e‖ := norm_add_le _ _
    _ ≤ ‖a - a * e‖ + ‖a - e * a‖ * ‖e‖ :=
      add_le_add le_rfl (norm_mul_le _ _)
    _ ≤ ‖a - a * e‖ + ‖a - e * a‖ := by
      apply add_le_add le_rfl
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hen (norm_nonneg (a - e * a))
    _ < ε := by linarith

def positiveCuntzSetoid : Setoid {a : A // 0 ≤ a} where
  r a b := CuntzSubequiv a.val b.val ∧ CuntzSubequiv b.val a.val
  iseqv := {
    refl := fun a => ⟨cstar_cuntzSubequiv_refl a.val, cstar_cuntzSubequiv_refl a.val⟩
    symm := fun h => h.symm
    trans := fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩ }

def PositiveCuntzClass (A : Type uA) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] := Quotient (positiveCuntzSetoid (A := A))

end

section

open Filter Topology

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem hereditary_cuntzSubequiv (h c : A) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (hcm : c ∈ hereditaryCarrier h) : CuntzSubequiv c h := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (hereditary_sqrt_mem hh hc hcm)
  have hs := (hlim.star.mul hlim)
  rw [(CFC.sqrt_nonneg c).star_eq, CFC.sqrt_mul_sqrt_self c hc] at hs
  apply cuntzSubequiv_of_tendsto (a := fun j => star (u j) * u j) _ hs
  intro j
  obtain ⟨w, hw⟩ := hu j
  rw [← hw]
  have hsquare : CFC.sqrt h * h * CFC.sqrt h = h * h := by
    calc
      _ = CFC.sqrt h * (CFC.sqrt h * CFC.sqrt h) * CFC.sqrt h := by
        rw [CFC.sqrt_mul_sqrt_self h hh]
      _ = (CFC.sqrt h * CFC.sqrt h) * (CFC.sqrt h * CFC.sqrt h) := by
        noncomm_ring
      _ = h * h := by rw [CFC.sqrt_mul_sqrt_self h hh]
  have heq : star (h * w * h) * (h * w * h) =
      star (CFC.sqrt h * w * h) * h * (CFC.sqrt h * w * h) := by
    simp only [star_mul, hh.star_eq, (CFC.sqrt_nonneg h).star_eq]
    calc
      _ = h * star w * (h * h) * w * h := by simp only [mul_assoc]
      _ = h * star w * (CFC.sqrt h * h * CFC.sqrt h) * w * h := by rw [hsquare]
      _ = _ := by simp only [mul_assoc]
  rw [heq]
  exact cuntzSubequiv_conjugate _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_mul_star_self (x : A) : ‖x * star x‖ = ‖x‖ * ‖x‖ := by
  simpa only [star_star, norm_star] using (CStarRing.norm_star_mul_self (x := star x))

omit [PartialOrder A] [StarOrderedRing A] in
lemma tendsto_mul_zero_of_norm_le_one (z e : ℕ → A)
    (hz : Tendsto z atTop (𝓝 0)) (he : ∀ n, ‖e n‖ ≤ 1) :
    Tendsto (fun n => z n * e n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa only [norm_zero] using hz.norm)
  calc
    _ ≤ ‖z n‖ * ‖e n‖ := norm_mul_le _ _
    _ ≤ ‖z n‖ * 1 := mul_le_mul_of_nonneg_left (he n) (norm_nonneg _)
    _ = ‖z n‖ := mul_one _

lemma normalizedRoot_mul_of_mul_star_self_tendsto (h x : A) (hh : 0 ≤ h)
    (hx : x * star x ∈ hereditaryCarrier h) :
    Tendsto (fun j => normalizedRoot h j * x) atTop (𝓝 x) := by
  let e := normalizedRoot h
  let z := fun j => x * star x - e j * (x * star x)
  have he (j : ℕ) : ‖e j‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg h j)).mpr
      (normalizedRoot_le_one h hh j)
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := x * star x)).sub
      (normalizedRoot_mul_hereditary_tendsto h hh _ hx)
  have hw : Tendsto (fun j => z j - z j * e j) atTop (𝓝 0) := by
    simpa only [sub_zero] using hz.sub (tendsto_mul_zero_of_norm_le_one z e hz he)
  have hn (j : ℕ) : ‖x - e j * x‖ ^ 2 = ‖z j - z j * e j‖ := by
    calc
      _ = ‖(x - e j * x) * star (x - e j * x)‖ := by
        rw [norm_mul_star_self, pow_two]
      _ = _ := by
        congr 1
        dsimp [z, e]
        simp only [star_sub, star_mul, (normalizedRoot_nonneg h j).star_eq]
        noncomm_ring
  have hsq : Tendsto (fun j => ‖x - e j * x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hn, norm_zero] using hw.norm
  have hzero : Tendsto (fun j => x - e j * x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := x)).sub hzero

theorem star_mul_self_cuntzSubequiv_of_hereditary (h x : A) (hh : 0 ≤ h)
    (hx : x * star x ∈ hereditaryCarrier h) : CuntzSubequiv (star x * x) h := by
  have ht : Tendsto (fun j => star x * normalizedRoot h j * x) atTop (𝓝 (star x * x)) := by
    simpa only [mul_assoc] using tendsto_const_nhds.mul
      (normalizedRoot_mul_of_mul_star_self_tendsto h x hh hx)
  apply cuntzSubequiv_of_tendsto _ ht
  intro j
  exact (hereditary_cuntzSubequiv h (normalizedRoot h j) hh (normalizedRoot_nonneg h j)
    (normalizedRoot_mem_hereditary hh (self_mem_hereditary h hh) hh j)).conjugate_left x

theorem star_mul_self_cuntzSubequiv (x : A) : CuntzSubequiv (star x * x) (x * star x) :=
  star_mul_self_cuntzSubequiv_of_hereditary _ x (mul_star_self_nonneg x)
    (self_mem_hereditary _ (mul_star_self_nonneg x))

theorem mul_star_self_cuntzSubequiv (x : A) : CuntzSubequiv (x * star x) (star x * x) := by
  simpa only [star_star] using star_mul_self_cuntzSubequiv (star x)

end

section

open scoped ComplexOrder

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_nonzero_cross (hsimple : TopologicallySimple A) (e f : A)
    (he : e ≠ 0) (hf : 0 ≤ f) (hf0 : f ≠ 0) : ∃ z : A, e * z * f ≠ 0 := by
  obtain ⟨n, s, hs⟩ := fullness hsimple f hf hf0
  by_contra hnone
  have hz (z : A) : e * z * f = 0 := by
    by_contra hne
    exact hnone ⟨z, hne⟩
  apply he
  calc
    e = e * (∑ i : Fin n, star (s i) * f * s i) := by rw [hs, mul_one]
    _ = ∑ i : Fin n, (e * star (s i) * f) * s i := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    _ = 0 := by simp only [hz, zero_mul, Finset.sum_const_zero]

theorem exists_common_minorant (hsimple : TopologicallySimple A) (e f : A)
    (he : 0 ≤ e) (he0 : e ≠ 0) (hf : 0 ≤ f) (hf0 : f ≠ 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧ CuntzSubequiv h e ∧ CuntzSubequiv h f ∧
      ∀ τ : TracialState A,
        normalizedRootRank τ h ≤ normalizedRootRank τ e ∧
        normalizedRootRank τ h ≤ normalizedRootRank τ f := by
  obtain ⟨z, hz⟩ := exists_nonzero_cross hsimple e f he0 hf hf0
  let v := e * z * f
  have hv : v ≠ 0 := hz
  have hvm : v * star v ∈ hereditaryCarrier e := by
    apply subset_closure
    refine ⟨z * f * f * star z, ?_⟩
    simp only [v, star_mul, he.star_eq, hf.star_eq, mul_assoc]
  have hsm : star v * v ∈ hereditaryCarrier f := by
    apply subset_closure
    refine ⟨star z * e * e * z, ?_⟩
    simp only [v, star_mul, he.star_eq, hf.star_eq, mul_assoc]
  have hne : star v * v ≠ 0 := by
    intro heq
    have hn : ‖v‖ * ‖v‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, heq, norm_zero]
    rcases mul_eq_zero.mp hn with hn | hn
    all_goals exact hv (norm_eq_zero.mp hn)
  refine ⟨star v * v, star_mul_self_nonneg v, hne, ?_,
    hereditary_cuntzSubequiv f _ hf (star_mul_self_nonneg v) hsm, ?_⟩
  · exact (star_mul_self_cuntzSubequiv v).trans
      (hereditary_cuntzSubequiv e _ he (mul_star_self_nonneg v) hvm)
  · intro τ
    constructor
    · rw [rank_star_mul_self τ v]
      exact hereditary_rank_domination τ e _ he (mul_star_self_nonneg v) hvm
    · exact hereditary_rank_domination τ f _ hf (star_mul_self_nonneg v) hsm

theorem exists_finite_common_minorant [Nontrivial A] (hsimple : TopologicallySimple A)
    {ι : Type uι} (I : Finset ι) (e : ι → A)
    (he : ∀ i ∈ I, 0 ≤ e i) (he0 : ∀ i ∈ I, e i ≠ 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧
      (∀ i ∈ I, CuntzSubequiv h (e i)) ∧
      (∀ τ : TracialState A, ∀ i ∈ I, normalizedRootRank τ h ≤ normalizedRootRank τ (e i)) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, zero_le_one, one_ne_zero, by simp, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨h, hh, hh0, hhC, hhR⟩ := ih
      (fun j hj => he j (Finset.mem_insert_of_mem hj))
      (fun j hj => he0 j (Finset.mem_insert_of_mem hj))
    obtain ⟨k, hk, hk0, hkh, hki, hkr⟩ := exists_common_minorant hsimple h (e i)
      hh hh0 (he i (Finset.mem_insert_self i I)) (he0 i (Finset.mem_insert_self i I))
    refine ⟨k, hk, hk0, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hki
      · exact hkh.trans (hhC j hj)
    · intro τ j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hkr τ).2
      · exact (hkr τ).1.trans (hhR τ j hj)

end

section

open Filter Topology

open scoped ComplexOrder ENNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_mul_eq_zero {h k x y : A}
    (hx : x ∈ hereditaryCarrier h) (hy : y ∈ hereditaryCarrier k) (hhk : h * k = 0) :
    x * y = 0 := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
  have hz (j : ℕ) : u j * v j = 0 := by
    obtain ⟨a, ha⟩ := hu j
    obtain ⟨b, hb⟩ := hv j
    rw [← ha, ← hb]
    calc
      _ = h * a * (h * k) * b * k := by simp only [mul_assoc]
      _ = 0 := by rw [hhk]; simp
  have ht := hux.mul hvy
  simp only [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma orthogonal_add_le_one (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hab : a * b = 0) : a + b ≤ 1 := by
  have hba : b * a = 0 := by
    simpa only [star_mul, ha.star_eq, hb.star_eq, star_zero] using congrArg star hab
  have hcomm : Commute (1 - a) (1 - b) := by
    show (1 - a) * (1 - b) = (1 - b) * (1 - a)
    noncomm_ring [hab, hba]
  have hpos := Commute.mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1) hcomm
  have heq : (1 - a) * (1 - b) = 1 - (a + b) := by noncomm_ring [hab]
  rw [heq] at hpos
  exact sub_nonneg.mp hpos

lemma orthogonal_sum_le_one {ι : Type uι} (I : Finset ι) (a : ι → A)
    (ha : ∀ i ∈ I, 0 ≤ a i) (ha1 : ∀ i ∈ I, a i ≤ 1)
    (horth : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → a i * a j = 0) :
    ∑ i ∈ I, a i ≤ 1 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    apply orthogonal_add_le_one (a i) (∑ j ∈ I, a j)
      (ha i (Finset.mem_insert_self i I))
      (Finset.sum_nonneg fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (ha1 i (Finset.mem_insert_self i I))
    · exact ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hjk => horth j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk)
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
        (fun heq => hi (heq ▸ hj))

theorem orthogonal_rank_sum_le_one (τ : TracialState A) {ι : Type uι} (I : Finset ι)
    (a : ι → A) (ha : ∀ i ∈ I, 0 ≤ a i)
    (horth : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → a i * a j = 0) :
    ∑ i ∈ I, normalizedRootRank τ (a i) ≤ 1 := by
  have ht : Tendsto (fun n => ∑ i ∈ I, ENNReal.ofReal (τ.functional (normalizedRoot (a i) n)).re)
      atTop (𝓝 (∑ i ∈ I, normalizedRootRank τ (a i))) :=
    tendsto_finsetSum I (fun i hi => normalizedRootRank_tendsto τ (a i) (ha i hi))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro n
  have hs : ∑ i ∈ I, normalizedRoot (a i) n ≤ 1 := by
    apply orthogonal_sum_le_one I (fun i => normalizedRoot (a i) n)
      (fun i _ => normalizedRoot_nonneg (a i) n)
      (fun i hi => normalizedRoot_le_one (a i) (ha i hi) n)
    intro i hi j hj hij
    exact hereditary_mul_eq_zero
      (normalizedRoot_mem_hereditary (ha i hi) (self_mem_hereditary _ (ha i hi)) (ha i hi) n)
      (normalizedRoot_mem_hereditary (ha j hj) (self_mem_hereditary _ (ha j hj)) (ha j hj) n)
      (horth i hi j hj hij)
  have hreal : (τ.functional (∑ i ∈ I, normalizedRoot (a i) n)).re ≤ 1 := by
    have hτ : τ.functional (∑ i ∈ I, normalizedRoot (a i) n) ≤ τ.functional 1 :=
      τ.functional.monotone hs
    rw [τ.normalized] at hτ
    exact (Complex.le_def.mp hτ).1
  have hn (i : ι) (hi : i ∈ I) : 0 ≤ (τ.functional (normalizedRoot (a i) n)).re :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (normalizedRoot_nonneg (a i) n))).1
  rw [← ENNReal.ofReal_sum_of_nonneg hn]
  apply ENNReal.ofReal_le_one.mpr
  simpa only [map_sum, Complex.re_sum] using hreal

theorem small_rank_of_orthogonal_family [Nontrivial A] (hsimple : TopologicallySimple A)
    (N : ℕ) (hN : 1 ≤ N) (a : Fin N → A) (ha : ∀ i, 0 ≤ a i)
    (ha0 : ∀ i, a i ≠ 0) (horth : ∀ i j, i ≠ j → a i * a j = 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧
      (∀ i, CuntzSubequiv h (a i)) ∧
      (∀ τ : TracialState A, normalizedRootRank τ h ≤ 1 / (N : ℝ≥0∞)) := by
  obtain ⟨h, hh, hh0, hhC, hhR⟩ := exists_finite_common_minorant hsimple Finset.univ a
    (fun i _ => ha i) (fun i _ => ha0 i)
  refine ⟨h, hh, hh0, fun i => hhC i (Finset.mem_univ i), ?_⟩
  intro τ
  have hsum : (N : ℝ≥0∞) * normalizedRootRank τ h ≤ 1 := by
    calc
      _ = ∑ i : Fin N, normalizedRootRank τ h := by simp [nsmul_eq_mul]
      _ ≤ ∑ i : Fin N, normalizedRootRank τ (a i) :=
        Finset.sum_le_sum (fun i hi => hhR τ i hi)
      _ ≤ 1 := orthogonal_rank_sum_le_one τ Finset.univ a
        (fun i _ => ha i) (fun i _ j _ hij => horth i j hij)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (Nat.ne_of_gt hN))) (by simp)).mpr
  simpa only [mul_comm] using hsum

end

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteDimensional_of_scalar_sandwich (hsimple : TopologicallySimple A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0)
    (hcorner : ∀ a : A, ∃ z : ℂ, h * a * h = z • h) : FiniteDimensional ℂ A := by
  classical
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hh0
  let g : Fin n × Fin n → A := fun ij => star (s ij.1) * h * s ij.2
  let T : (Fin n × Fin n → ℂ) →ₗ[ℂ] A := {
    toFun := fun c => ∑ ij, c ij • g ij
    map_add' := by
      intro c d
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro z c
      simp only [Pi.smul_apply, smul_smul, smul_eq_mul, Finset.smul_sum, RingHom.id_apply] }
  apply Module.Finite.of_surjective T
  intro a
  choose c hc using fun i j : Fin n => hcorner (s i * a * star (s j))
  refine ⟨fun ij => c ij.1 ij.2, ?_⟩
  change (∑ ij : Fin n × Fin n, c ij.1 ij.2 • g ij) = a
  symm
  calc
    a = (∑ i : Fin n, star (s i) * h * s i) * a *
        (∑ j : Fin n, star (s j) * h * s j) := by rw [hs, one_mul, mul_one]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        star (s i) * (h * (s i * a * star (s j)) * h) * s j := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, c i j • (star (s i) * h * s j) := by
      simp only [hc, mul_smul_comm, smul_mul_assoc]
    _ = _ := by simp only [Fintype.sum_prod_type, g]

theorem exists_nonscalar_sandwich (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) :
    ∃ a : A, ∀ z : ℂ, h * a * h ≠ z • h := by
  by_contra hn
  push Not at hn
  exact hinf (finiteDimensional_of_scalar_sandwich hsimple h hh hh0 hn)

end Pureness

end

end OAI
