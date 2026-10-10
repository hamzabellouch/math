import OAI.Analysis.TracialSplitting.Completion

namespace OAI

noncomputable section

universe uA uD uE uI uS uX

namespace CurrentMain

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

lemma exists_coordinate_split (K : Finset D) {ε : ℝ} (hε : 0 < ε)
    {P : FamilyUltrapower τ U} (hP : IsStarProjection P)
    (hc : ∀ x ∈ K, familyTwoNorm (familyLimitTrace τ U)
      (P * familyUltrapowerMap τ U x - familyUltrapowerMap τ U x * P) < ε)
    (hh : ∀ x ∈ K, familyTraceNorm (familyLimitTrace τ U)
      (P * familyUltrapowerMap τ U x - (1/2 : ℂ) • familyUltrapowerMap τ U x) < ε) :
    ∃ b : D, IsSelfAdjoint b ∧ ‖b‖ ≤ 2 ∧ familyTwoNorm τ (b*b-b) < ε ∧
      ∀ x ∈ K, familyTwoNorm τ (b*x-x*b) < ε ∧
        familyTraceNorm τ (b*x-(1/2 : ℂ) • x) < ε := by
  let q := (familyNullIdeal τ (U : Filter X)).quotientMap
  obtain ⟨c,hcsa,hcn,hcq⟩ :=
    (familyNullIdeal τ (U : Filter X)).exists_bounded_selfAdjoint_lift hP
  have hd : IsFamilyNull τ (U : Filter X) (fun j => c j*c j-c j) := by
    apply (familyQuotientMap_eq_zero τ U (c*c-c)).mp
    rw [map_sub, map_mul, hcq, hP.isIdempotentElem.eq, sub_self]
  have hc' (x : D) (hx : x ∈ K) : ∀ᶠ j in (U : Filter X),
      familyTwoNorm τ (c j*x-x*c j) < ε := by
    have ht := familyTwoNorm_limitTrace_tendsto τ U
      (c * boundedFamilyConstant x - boundedFamilyConstant x * c)
    have he : q (c * boundedFamilyConstant x - boundedFamilyConstant x * c) =
        P * familyUltrapowerMap τ U x - familyUltrapowerMap τ U x * P := by
      rw [map_sub, map_mul, map_mul]
      exact congrArg₂ (fun a b => a * familyUltrapowerMap τ U x -
        familyUltrapowerMap τ U x * b) hcq hcq
    change Tendsto (fun j => familyTwoNorm τ (c j*x-x*c j)) _ (𝓝 (familyTwoNorm _
      (q (c * boundedFamilyConstant x - boundedFamilyConstant x * c)))) at ht
    rw [he] at ht
    exact ht.eventually (gt_mem_nhds (hc x hx))
  have hh' (x : D) (hx : x ∈ K) : ∀ᶠ j in (U : Filter X),
      familyTraceNorm τ (c j*x-(1/2 : ℂ) • x) < ε := by
    have ht := familyTraceNorm_limitTrace_tendsto τ U
      (c * boundedFamilyConstant x - (1/2 : ℂ) • boundedFamilyConstant x)
    have he : q (c * boundedFamilyConstant x - (1/2 : ℂ) • boundedFamilyConstant x) =
        P * familyUltrapowerMap τ U x - (1/2 : ℂ) • familyUltrapowerMap τ U x := by
      rw [map_sub, map_mul, map_smul]
      exact congrArg (fun a => a * familyUltrapowerMap τ U x -
        (1/2 : ℂ) • familyUltrapowerMap τ U x) hcq
    change Tendsto (fun j => familyTraceNorm τ (c j*x-(1/2 : ℂ) • x)) _
      (𝓝 (familyTraceNorm _ (q (c * boundedFamilyConstant x -
        (1/2 : ℂ) • boundedFamilyConstant x)))) at ht
    rw [he] at ht
    exact ht.eventually (gt_mem_nhds (hh x hx))
  have hevent : ∀ᶠ j in (U : Filter X), familyTwoNorm τ (c j*c j-c j) < ε ∧
      ∀ x ∈ K, familyTwoNorm τ (c j*x-x*c j) < ε ∧
        familyTraceNorm τ (c j*x-(1/2 : ℂ) • x) < ε :=
    ((isFamilyNull_iff τ _ _).mp hd ε hε).and
      ((eventually_all_finset K).mpr (fun x hx => (hc' x hx).and (hh' x hx)))
  obtain ⟨j,hj⟩ := hevent.exists
  refine ⟨c j,?_,(lp.norm_apply_le_norm ENNReal.top_ne_zero c j).trans hcn,hj⟩
  exact congrArg (fun a : lp (fun _ : X => D) ∞ => a j) hcsa.star_eq

end

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter ℕ)

lemma projection_of_bounded_sequence (c : lp (fun _ : ℕ => D) ∞)
    (hsa : ∀ n, IsSelfAdjoint (c n))
    (hd : IsFamilyNull τ (U : Filter ℕ) (fun n => c n*c n-c n)) :
    IsStarProjection ((familyNullIdeal τ (U : Filter ℕ)).quotientMap c) := by
  have hcsa : star c = c := by
    apply lp.ext
    funext n
    exact (hsa n).star_eq
  refine ⟨?_,?_⟩
  · have he := (familyQuotientMap_eq_zero τ U (c*c-c)).mpr hd
    rw [map_sub, map_mul, sub_eq_zero] at he
    exact he
  · change star ((familyNullIdeal τ (U : Filter ℕ)).quotientMap c) = _
    rw [← ClosedStarIdeal.quotientMap_star,hcsa]

lemma commute_of_null_sequence (c : lp (fun _ : ℕ => D) ∞) (a : D)
    (hc : IsFamilyNull τ (U : Filter ℕ) (fun n => c n*a-a*c n)) :
    (familyNullIdeal τ (U : Filter ℕ)).quotientMap c * familyUltrapowerMap τ U a =
      familyUltrapowerMap τ U a * (familyNullIdeal τ (U : Filter ℕ)).quotientMap c := by
  let v : lp (fun _ : ℕ => D) ∞ := boundedFamilyConstant a
  have hv : IsFamilyNull τ (U : Filter ℕ) (fun n => (c*v-v*c) n) := by
    exact hc
  have he := (familyQuotientMap_eq_zero τ U (c*v-v*c)).mpr hv
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at he
  exact he

lemma halftrace_of_null_sequence (c : lp (fun _ : ℕ => D) ∞) (a : D)
    (hh : Tendsto (fun n => familyTraceNorm τ (c n*a-(1/2 : ℂ) • a))
      (U : Filter ℕ) (𝓝 0)) (s : ℕ → I) :
    (familyLimitTrace τ U s).functional
      ((familyNullIdeal τ (U : Filter ℕ)).quotientMap c * familyUltrapowerMap τ U a) =
      (1/2 : ℂ) * (familyLimitTrace τ U s).functional (familyUltrapowerMap τ U a) := by
  let q := (familyNullIdeal τ (U : Filter ℕ)).quotientMap
  have hz : familyTraceNorm (familyLimitTrace τ U)
      (q (c*boundedFamilyConstant a-(1/2 : ℂ) • boundedFamilyConstant a)) = 0 :=
    tendsto_nhds_unique (familyTraceNorm_limitTrace_tendsto τ U _) hh
  have hs : (familyLimitTrace τ U s).functional
      (q (c*boundedFamilyConstant a-(1/2 : ℂ) • boundedFamilyConstant a)) = 0 :=
    norm_eq_zero.mp (le_antisymm ((traceNorm_le_family _ s _).trans hz.le) (norm_nonneg _))
  rw [map_sub, map_mul, map_smul, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hs
  exact hs

theorem diagonalize_finite_splittings (hfree : (U : Filter ℕ) ≤ atTop)
    (x : ℕ → D)
    (hfinite : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ P : FamilyUltrapower τ U,
      IsStarProjection P ∧ ∀ k ≤ n,
        familyTwoNorm (familyLimitTrace τ U)
          (P * familyUltrapowerMap τ U (x k) - familyUltrapowerMap τ U (x k) * P) < ε ∧
        familyTraceNorm (familyLimitTrace τ U)
          (P * familyUltrapowerMap τ U (x k) -
            (1/2 : ℂ) • familyUltrapowerMap τ U (x k)) < ε) :
    ∃ p : FamilyUltrapower τ U, IsStarProjection p ∧ ∀ k : ℕ,
      p * familyUltrapowerMap τ U (x k) = familyUltrapowerMap τ U (x k) * p ∧
      ∀ s : ℕ → I, (familyLimitTrace τ U s).functional (p * familyUltrapowerMap τ U (x k)) =
        (1/2 : ℂ) * (familyLimitTrace τ U s).functional (familyUltrapowerMap τ U (x k)) := by
  classical
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hetend : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (n : ℕ) : ∃ b : D, IsSelfAdjoint b ∧ ‖b‖ ≤ 2 ∧
      familyTwoNorm τ (b*b-b) < e n ∧ ∀ k ≤ n,
        familyTwoNorm τ (b*x k-x k*b) < e n ∧
        familyTraceNorm τ (b*x k-(1/2 : ℂ) • x k) < e n := by
    obtain ⟨P,hP,hPtest⟩ := hfinite n (e n) (hepos n)
    have hm {a : D} (ha : a ∈ (Finset.range (n+1)).image x) :
        ∃ k ≤ n, x k = a := by
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ha
      exact ⟨k,Nat.lt_succ_iff.mp (Finset.mem_range.mp hk),rfl⟩
    obtain ⟨b,hbsa,hbn,hbd,hbt⟩ := exists_coordinate_split τ U
      ((Finset.range (n+1)).image x) (hepos n) hP
      (by intro a ha; obtain ⟨k,hk,rfl⟩ := hm ha; exact (hPtest k hk).1)
      (by intro a ha; obtain ⟨k,hk,rfl⟩ := hm ha; exact (hPtest k hk).2)
    refine ⟨b,hbsa,hbn,hbd,fun k hk => hbt (x k) ?_⟩
    exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk),rfl⟩
  choose b hbsa hbn hbd hbt using hb
  let c : lp (fun _ : ℕ => D) ∞ :=
    ⟨b,memℓp_infty_iff.mpr ⟨2,by rintro _ ⟨n,rfl⟩; exact hbn n⟩⟩
  have hd : IsFamilyNull τ (U : Filter ℕ) (fun n => c n*c n-c n) := by
    exact (squeeze_zero (fun _ => familyTwoNorm_nonneg τ _)
      (fun n => (hbd n).le) hetend).mono_left hfree
  refine ⟨(familyNullIdeal τ (U : Filter ℕ)).quotientMap c,
    projection_of_bounded_sequence τ U c hbsa hd,fun k => ⟨?_,?_⟩⟩
  · apply commute_of_null_sequence τ U c (x k)
    apply Tendsto.mono_left _ hfree
    apply squeeze_zero' (Eventually.of_forall (fun _ => familyTwoNorm_nonneg τ _)) _ hetend
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (hbt n k hn).1.le
  · apply halftrace_of_null_sequence τ U c (x k)
    apply Tendsto.mono_left _ hfree
    apply squeeze_zero' (Eventually.of_forall (fun _ => familyTraceNorm_nonneg τ _)) _ hetend
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (hbt n k hn).2.le

end

section

open Pureness

open scoped ComplexOrder

section DenseUnitaryExtension

variable {A : Type uA} {E : Type uE} [CStarAlgebra A] [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma linearMap_zero_of_dense_unitaries (u : ℕ → unitary A) (hu : DenseRange u)
    (L : A →ₗ[ℂ] E) (hL : Continuous L) (hzero : ∀ n, L (u n : A) = 0) :
    ∀ a : A, L a = 0 := by
  have hunit : ∀ v : unitary A, L (v : A) = 0 := by
    exact congrFun (hu.equalizer (hL.comp continuous_subtype_val) continuous_const
      (funext hzero))
  have hspan : Submodule.span ℂ (unitary A : Set A) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    intro a ha
    exact hunit ⟨a,ha⟩
  rw [CStarAlgebra.span_unitary A] at hspan
  intro a
  exact hspan (Submodule.mem_top : a ∈ (⊤ : Submodule ℂ A))

end DenseUnitaryExtension

variable {A : Type uA} {E : Type uE} {S : Type uS} [CStarAlgebra A] [CStarAlgebra E]

variable [PartialOrder E] [StarOrderedRing E]

lemma splitting_of_dense_unitaries (ι : A →⋆ₐ[ℂ] E) (σ : S → TracialState E)
    (p : E) (u : ℕ → unitary A) (hu : DenseRange u)
    (htest : ∀ n, p * ι (u n : A) = ι (u n : A) * p ∧
      ∀ s, (σ s).functional (p * ι (u n : A)) = (1/2 : ℂ) * (σ s).functional (ι (u n : A))) :
    ∀ a : A, p * ι a = ι a * p ∧
      ∀ s, (σ s).functional (p * ι a) = (1/2 : ℂ) * (σ s).functional (ι a) := by
  have hι : Continuous ι := AddMonoidHomClass.continuous_of_bound ι 1 (fun a => by
    simpa only [one_mul] using (NonUnitalStarAlgHom.norm_apply_le ι a))
  let L : A →ₗ[ℂ] E :=
    (LinearMap.mulLeft ℂ p - LinearMap.mulRight ℂ p).comp ι.toLinearMap
  have hc : ∀ a, L a = 0 := linearMap_zero_of_dense_unitaries u hu L
    ((continuous_const.mul hι).sub (hι.mul continuous_const))
    (fun n => sub_eq_zero.mpr (htest n).1)
  have hh (s : S) : ∀ a : A,
      (σ s).functional (p * ι a) - (1/2 : ℂ) * (σ s).functional (ι a) = 0 := by
    let M : A →ₗ[ℂ] ℂ :=
      (σ s).functional.toLinearMap.comp ((LinearMap.mulLeft ℂ p).comp ι.toLinearMap) -
        (1/2 : ℂ) • ((σ s).functional.toLinearMap.comp ι.toLinearMap)
    have hσ : Continuous (σ s).functional := map_continuous (σ s).functional
    exact linearMap_zero_of_dense_unitaries u hu M
      ((hσ.comp (continuous_const.mul hι)).sub (continuous_const.mul (hσ.comp hι)))
      (fun n => sub_eq_zero.mpr ((htest n).2 s))
  exact fun a => ⟨sub_eq_zero.mp (hc a),fun s => sub_eq_zero.mp (hh s a)⟩

end

section

open Pureness

open scoped ComplexOrder

variable {E : Type uE} {S : Type uS} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

variable (σ : S → TracialState E) [Nonempty S]

lemma commutator_twoNorm_bound {p a b : E} (hp : ‖p‖ ≤ 1) (hb : p*b=b*p) :
    familyTwoNorm σ (p*a-a*p) ≤ 2 * familyTwoNorm σ (a-b) := by
  have he : p*a-a*p = p*(a-b)-(a-b)*p := by
    rw [mul_sub,sub_mul,hb]
    noncomm_ring
  rw [he]
  have h₁ := familyTwoNorm_mul_left σ p (a-b)
  have h₂ := familyTwoNorm_mul_right σ (a-b) p
  have hn := familyTwoNorm_nonneg σ (a-b)
  have ht := familyTwoNorm_sub_le σ (p*(a-b)) ((a-b)*p)
  nlinarith

lemma coefficient_half_error_bound (τ : TracialState E) {p a b : E} (hp : ‖p‖ ≤ 1)
    (hb : τ.functional (p*b) = (1/2 : ℂ) * τ.functional b) :
    ‖τ.functional (p*a) - (1/2 : ℂ) * τ.functional a‖ ≤
      (3/2 : ℝ) * traceTwoNorm τ (a-b) := by
  have he : τ.functional (p*a) - (1/2 : ℂ) * τ.functional a =
      τ.functional (p*(a-b)) - (1/2 : ℂ) * τ.functional (a-b) := by
    rw [mul_sub,map_sub,map_sub,hb]
    ring
  rw [he]
  have hn := traceTwoNorm_nonneg τ (a-b)
  have h₁ := (trace_norm_le_twoNorm τ (p*(a-b))).trans
    (traceTwoNorm_mul_left τ p (a-b))
  have h₂ : ‖(1/2 : ℂ) * τ.functional (a-b)‖ ≤ (1/2 : ℝ) * traceTwoNorm τ (a-b) := by
    rw [norm_mul]
    norm_num only [norm_div,norm_one,Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (trace_norm_le_twoNorm τ (a-b)) (by norm_num)
  have ht := norm_sub_le (τ.functional (p*(a-b))) ((1/2 : ℂ) * τ.functional (a-b))
  nlinarith

lemma splitting_of_uniform_approximants
    (hdetect : ∀ z : E, (∀ s, traceTwoNorm (σ s) z = 0) → z = 0)
    {p x : E} (hp : IsStarProjection p)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ b : E, familyTwoNorm σ (x-b) < ε ∧
      p*b=b*p ∧ ∀ s, (σ s).functional (p*b) = (1/2 : ℂ) * (σ s).functional b) :
    p*x=x*p ∧ ∀ s, (σ s).functional (p*x) = (1/2 : ℂ) * (σ s).functional x := by
  have hn : familyTwoNorm σ (p*x-x*p) = 0 := by
    apply le_antisymm _ (familyTwoNorm_nonneg σ _)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b,hb,hbc,_⟩ := happrox (ε/4) (by linarith)
    have ht := commutator_twoNorm_bound σ (a := x) (hp.norm_le p) hbc
    change familyTwoNorm σ (p*x-x*p) ≤ 0+ε
    linarith
  refine ⟨sub_eq_zero.mp (hdetect _ (fun s => ?_)),fun s => ?_⟩
  · exact le_antisymm ((traceTwoNorm_le_family σ s _).trans hn.le) (traceTwoNorm_nonneg _ _)
  · apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b,hb,_,hbh⟩ := happrox (ε/4) (by linarith)
    have ht := coefficient_half_error_bound (σ s) (a := x) (hp.norm_le p) (hbh s)
    have hl := traceTwoNorm_le_family σ s (x-b)
    change ‖(σ s).functional (p*x) - (1/2 : ℂ) * (σ s).functional x‖ ≤ 0+ε
    linarith

end

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {A : Type uA} {I : Type uI} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Nontrivial A] [TopologicalSpace.SeparableSpace A]

variable (τ : I → TracialState A) [Nonempty I] (U : Ultrafilter ℕ)

theorem completion_central_splitting_of_finite_stages
    (hfree : (U : Filter ℕ) ≤ atTop)
    (hfinite : ∀ (K : Finset (unitary A)) (ε : ℝ), 0 < ε →
      ∃ P : FamilyUltrapower (completionTrace τ) U, IsStarProjection P ∧ ∀ u ∈ K,
        familyTwoNorm (familyLimitTrace (completionTrace τ) U)
          (P * familyUltrapowerMap (completionTrace τ) U (completionMap τ (u : A)) -
           familyUltrapowerMap (completionTrace τ) U (completionMap τ (u : A)) * P) < ε ∧
        familyTraceNorm (familyLimitTrace (completionTrace τ) U)
          (P * familyUltrapowerMap (completionTrace τ) U (completionMap τ (u : A)) -
           (1/2 : ℂ) • familyUltrapowerMap (completionTrace τ) U (completionMap τ (u : A))) < ε) :
    ∃ p : FamilyUltrapower (completionTrace τ) U, IsStarProjection p ∧
      ∀ x : UniformTracialCompletion τ,
        p * familyUltrapowerMap (completionTrace τ) U x =
          familyUltrapowerMap (completionTrace τ) U x * p ∧
        ∀ s : ℕ → I, (familyLimitTrace (completionTrace τ) U s).functional
          (p * familyUltrapowerMap (completionTrace τ) U x) =
          (1/2 : ℂ) * (familyLimitTrace (completionTrace τ) U s).functional
            (familyUltrapowerMap (completionTrace τ) U x) := by
  classical
  obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq (unitary A)
  let j : A →⋆ₐ[ℂ] FamilyUltrapower (completionTrace τ) U :=
    (familyUltrapowerMap (completionTrace τ) U).comp (completionMap τ)
  have hstage (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∃ P : FamilyUltrapower (completionTrace τ) U, IsStarProjection P ∧ ∀ k ≤ n,
        familyTwoNorm (familyLimitTrace (completionTrace τ) U)
          (P * j (u k : A) - j (u k : A) * P) < ε ∧
        familyTraceNorm (familyLimitTrace (completionTrace τ) U)
          (P * j (u k : A) - (1/2 : ℂ) • j (u k : A)) < ε := by
    obtain ⟨P,hP,htest⟩ := hfinite ((Finset.range (n+1)).image u) ε hε
    refine ⟨P,hP,fun k hk => htest (u k) ?_⟩
    exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk),rfl⟩
  obtain ⟨p,hp,hptest⟩ := diagonalize_finite_splittings (completionTrace τ) U hfree
    (fun n => completionMap τ (u n : A)) hstage
  have hA := splitting_of_dense_unitaries j (familyLimitTrace (completionTrace τ) U) p u hu hptest
  refine ⟨p,hp,fun x => ?_⟩
  apply splitting_of_uniform_approximants (familyLimitTrace (completionTrace τ) U)
    (limitTrace_detects_zero (completionTrace τ) U) hp
  intro ε hε
  obtain ⟨a,ha⟩ := completion_uniform_dense τ x hε
  refine ⟨j a,?_,(hA a).1,(hA a).2⟩
  change familyTwoNorm (familyLimitTrace (completionTrace τ) U)
    (familyUltrapowerMap (completionTrace τ) U x -
      familyUltrapowerMap (completionTrace τ) U (completionMap τ a)) < ε
  rw [← map_sub,familyTwoNorm_ultrapowerMap]
  exact ha

end CurrentMain

end

end OAI
