import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology

open Filter

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def principalRightIdeal (a : A) : Submodule ℂ A :=
  (LinearMap.range (LinearMap.mulLeft ℂ a)).topologicalClosure

instance (a : A) : IsClosed (principalRightIdeal a : Set A) :=
  Submodule.isClosed_topologicalClosure _

instance (a : A) : CompleteSpace (principalRightIdeal a) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def principalRightMap (a : A) : A →ₗ[ℂ] principalRightIdeal a :=
  (LinearMap.mulLeft ℂ a).codRestrict _ (fun b =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ b))

omit [PartialOrder A] [StarOrderedRing A] in
lemma principalRightMap_dense (a : A) : DenseRange (principalRightMap a) := by
  have h : DenseRange (Set.inclusion (show Set.range (fun b : A => a*b) ⊆
      closure (Set.range (fun b : A => a*b)) from subset_closure) ∘
      Set.rangeFactorization (fun b : A => a*b)) :=
    ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
      Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
  exact h

lemma norm_mul_abs (x b : A) : ‖CFC.abs x * b‖ = ‖x * b‖ := by
  have heq : star (CFC.abs x * b) * (CFC.abs x * b) = star (x*b) * (x*b) := by
    rw [star_mul, (CFC.abs_nonneg x).star_eq, star_mul]
    calc
      star b * CFC.abs x * (CFC.abs x * b) =
          star b * (CFC.abs x * CFC.abs x) * b := by noncomm_ring
      _ = star b * (star x * x) * b := by rw [CFC.abs_mul_abs]
      _ = star b * star x * (x*b) := by noncomm_ring
  have hn := congrArg norm heq
  rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (CFC.abs x * b), norm_nonneg (x * b)]

def partialPolar (x : A) : principalRightIdeal (CFC.abs x) →L[ℂ] A :=
  (LinearMap.mulLeft ℂ x).extendOfNorm (principalRightMap (CFC.abs x))

lemma partialPolar_apply_mul (x b : A) :
    partialPolar x (principalRightMap (CFC.abs x) b) = x*b := by
  apply LinearMap.extendOfNorm_eq (principalRightMap_dense _)
  refine ⟨1, fun c => ?_⟩
  change ‖x*c‖ ≤ 1 * ‖CFC.abs x*c‖
  rw [one_mul, norm_mul_abs]

lemma partialPolar_norm (x : A) (a : principalRightIdeal (CFC.abs x)) :
    ‖partialPolar x a‖ = ‖a‖ := by
  refine (principalRightMap_dense (CFC.abs x)).induction_on a ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro b
    rw [partialPolar_apply_mul]
    exact (norm_mul_abs x b).symm

lemma partialPolar_initial_square (x : A) (a : principalRightIdeal (CFC.abs x)) :
    star (partialPolar x a) * partialPolar x a = star (a : A) * (a : A) := by
  refine (principalRightMap_dense (CFC.abs x)).induction_on a ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro b
    rw [partialPolar_apply_mul]
    change star (x*b) * (x*b) = star (CFC.abs x*b) * (CFC.abs x*b)
    rw [star_mul, star_mul, (CFC.abs_nonneg x).star_eq]
    calc
      star b * star x * (x*b) = star b * (star x*x) * b := by noncomm_ring
      _ = star b * (CFC.abs x*CFC.abs x) * b := by rw [CFC.abs_mul_abs]
      _ = star b * CFC.abs x * (CFC.abs x*b) := by noncomm_ring

lemma partialPolar_mem_rightIdeal (x : A) (a : principalRightIdeal (CFC.abs x)) :
    partialPolar x a ∈ principalRightIdeal x := by
  refine (principalRightMap_dense (CFC.abs x)).induction_on a ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage (partialPolar x).continuous
  · intro b
    rw [partialPolar_apply_mul]
    exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ b)

def sandwichSubalgebra (h : A) (hh : IsSelfAdjoint h) : NonUnitalStarSubalgebra ℂ A where
  carrier := Set.range (fun b : A => h*b*h)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨b+c, by noncomm_ring⟩
  smul_mem' := by
    rintro c _ ⟨b, rfl⟩
    exact ⟨c • b, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨b*h*h*c, by noncomm_ring⟩
  star_mem' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨star b, by simp only [star_mul, hh.star_eq]; noncomm_ring⟩

def hereditarySubalgebra (h : A) (hh : IsSelfAdjoint h) : NonUnitalStarSubalgebra ℂ A :=
  (sandwichSubalgebra h hh).topologicalClosure

instance (h : A) (hh : IsSelfAdjoint h) :
    IsClosed (hereditarySubalgebra h hh : Set A) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

instance (h : A) (hh : IsSelfAdjoint h) : CompleteSpace (hereditarySubalgebra h hh) :=
  (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).isComplete.completeSpace_coe

omit [PartialOrder A] [StarOrderedRing A] in
lemma sandwich_mem (h b : A) (hh : IsSelfAdjoint h) : h*b*h ∈ hereditarySubalgebra h hh :=
  (sandwichSubalgebra h hh).le_topologicalClosure ⟨b, rfl⟩

lemma square_mem_hereditary (h : A) (hh : IsSelfAdjoint h) :
    h*h ∈ hereditarySubalgebra h hh := by
  have ht : Tendsto (fun e : A => h*e*h) (CStarAlgebra.approximateUnit A) (𝓝 (h*h)) :=
    ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const h
  exact (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).mem_of_tendsto ht
    (Eventually.of_forall (fun e => sandwich_mem h e hh))

lemma sqrt_mem_hereditary (h x : A) (hh : IsSelfAdjoint h)
    (hx : x ∈ hereditarySubalgebra h hh) (hxpos : 0 ≤ x) :
    CFC.sqrt x ∈ hereditarySubalgebra h hh := by
  rw [CFC.sqrt_eq_real_sqrt x hxpos]
  exact cfcₙ_mem Real.sqrt hx

lemma self_mem_hereditary (h : A) (hh : 0 ≤ h) :
    h ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  convert sqrt_mem_hereditary h (h*h) hh.isSelfAdjoint
    (square_mem_hereditary h hh.isSelfAdjoint) (by simpa only [hh.star_eq] using star_mul_self_nonneg h) using 1
  exact (CFC.sqrt_mul_self h hh).symm

omit [PartialOrder A] [StarOrderedRing A] in
lemma principalRightIdeal_mul_mem (h a b : A) (ha : a ∈ principalRightIdeal h) :
    a*b ∈ principalRightIdeal h := by
  have hc : IsClosed {a : A | a*b ∈ principalRightIdeal h} :=
    (Submodule.isClosed_topologicalClosure _).preimage (continuous_id.mul_const b)
  apply closure_minimal _ hc ha
  rintro _ ⟨c, rfl⟩
  exact Submodule.le_topologicalClosure _ ⟨c*b, by change h*(c*b) = (h*c)*b; simp only [mul_assoc]⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_le_rightIdeal (h : A) (hh : IsSelfAdjoint h) :
    (hereditarySubalgebra h hh : Set A) ⊆ principalRightIdeal h := by
  apply closure_minimal _ (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨b, rfl⟩
  exact Submodule.le_topologicalClosure _ ⟨b*h, by change h*(b*h) = h*b*h; simp only [mul_assoc]⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma rightIdeal_square_mem_hereditary (h a : A) (hh : IsSelfAdjoint h)
    (ha : a ∈ principalRightIdeal h) : a * star a ∈ hereditarySubalgebra h hh := by
  have hc : IsClosed {a : A | a * star a ∈ hereditarySubalgebra h hh} :=
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage (by fun_prop)
  apply closure_minimal _ hc ha
  rintro _ ⟨b, rfl⟩
  change (h*b)*star (h*b) ∈ hereditarySubalgebra h hh
  convert sandwich_mem h (b*star b) hh using 1
  simp only [star_mul, hh.star_eq, mul_assoc]

def residual (e h : A) := h - e*h - h*e + e*h*e

lemma residual_nonneg (e h : A) (he : IsSelfAdjoint e) (hh : 0 ≤ h) :
    0 ≤ residual e h := by
  have hs : CFC.sqrt h * CFC.sqrt h = h := CFC.sqrt_mul_sqrt_self h hh
  convert mul_star_self_nonneg (CFC.sqrt h-e*CFC.sqrt h) using 1
  simp only [residual, star_sub, star_mul, (CFC.sqrt_nonneg h).star_eq, he.star_eq]
  rw [show (CFC.sqrt h-e*CFC.sqrt h) * (CFC.sqrt h-CFC.sqrt h*e) =
    CFC.sqrt h*CFC.sqrt h-e*(CFC.sqrt h*CFC.sqrt h) -
      (CFC.sqrt h*CFC.sqrt h)*e+e*(CFC.sqrt h*CFC.sqrt h)*e by noncomm_ring, hs]

lemma residual_mono (e : A) (he : IsSelfAdjoint e) {h k : A} (hkh : h ≤ k) :
    residual e h ≤ residual e k := by
  apply sub_nonneg.mp
  convert residual_nonneg e (k-h) he (sub_nonneg.mpr hkh) using 1
  simp only [residual]
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma residual_square (e a : A) (he : IsSelfAdjoint e) :
    residual e (a*star a) = (a-e*a)*star (a-e*a) := by
  simp only [residual, star_sub, star_mul, he.star_eq]
  noncomm_ring

lemma norm_sub_left_mul_sq_le (e h a : A) (he : IsSelfAdjoint e)
    (ha : a*star a ≤ h) : ‖a-e*a‖^2 ≤ ‖residual e h‖ := by
  have hb := CStarAlgebra.norm_le_norm_of_le_of_nonneg (residual_mono e he ha)
    (residual_nonneg e (a*star a) he (mul_star_self_nonneg a))
  rw [residual_square e a he, CStarRing.norm_self_mul_star] at hb
  simpa only [pow_two] using hb

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_residual_le (e h : A) (he : ‖e‖ ≤ 1) :
    ‖residual e h‖ ≤ 2 * ‖h-e*h‖ := by
  have hr : residual e h = (h-e*h) - (h-e*h)*e := by
    simp only [residual]
    noncomm_ring
  rw [hr]
  calc
    ‖(h-e*h) - (h-e*h)*e‖ ≤ ‖h-e*h‖ + ‖(h-e*h)*e‖ := norm_sub_le _ _
    _ ≤ ‖h-e*h‖ + ‖h-e*h‖*‖e‖ := add_le_add le_rfl (norm_mul_le _ _)
    _ ≤ ‖h-e*h‖ + ‖h-e*h‖*1 := by gcongr
    _ = 2*‖h-e*h‖ := by ring

lemma norm_sub_left_mul_le_sqrt (e h a : A) (he : IsSelfAdjoint e) (hen : ‖e‖ ≤ 1)
    (ha : a*star a ≤ h) : ‖a-e*a‖ ≤ Real.sqrt (2*‖h-e*h‖) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  exact (norm_sub_left_mul_sq_le e h a he ha).trans (norm_residual_le e h hen)

lemma principalRightIdeal_of_square_le (h a : A) (hh : 0 ≤ h) (ha : a*star a ≤ h) :
    a ∈ principalRightIdeal h := by
  let S := hereditarySubalgebra h hh.isSelfAdjoint
  let := CStarAlgebra.spectralOrder S
  let := CStarAlgebra.spectralOrderedRing S
  let h₀ : S := ⟨h, self_mem_hereditary h hh⟩
  let F := CStarAlgebra.approximateUnit S
  have hF := CStarAlgebra.increasingApproximateUnit S
  have ht : Tendsto (fun e : S => (e:A)*h) F (𝓝 h) := by
    exact (continuous_subtype_val.tendsto h₀).comp (hF.tendsto_mul_right h₀)
  have hd : Tendsto (fun e : S => ‖h-(e:A)*h‖) F (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : S => h) F (𝓝 h)).sub ht).norm
  have hb : Tendsto (fun e : S => Real.sqrt (2*‖h-(e:A)*h‖)) F (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero] using (hd.const_mul 2).sqrt
  have hn : Tendsto (fun e : S => ‖a-(e:A)*a‖) F (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
    filter_upwards [hF.eventually_isSelfAdjoint, hF.eventually_norm] with e he hen
    exact norm_sub_left_mul_le_sqrt (e:A) h a
      (show IsSelfAdjoint (e:A) from congrArg Subtype.val he) hen ha
  have ht' : Tendsto (fun e : S => (e:A)*a) F (𝓝 a) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [norm_sub_rev] using hn
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht'
    (Eventually.of_forall (fun e => principalRightIdeal_mul_mem h (e:A) a
      (hereditary_le_rightIdeal h hh.isSelfAdjoint e.property)))

lemma mem_hereditary_of_le (h x : A) (hh : 0 ≤ h) (hx : 0 ≤ x) (hxh : x ≤ h) :
    x ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  have hs : CFC.sqrt x * star (CFC.sqrt x) = x := by
    rw [(CFC.sqrt_nonneg x).star_eq, CFC.sqrt_mul_sqrt_self x hx]
  rw [← hs]
  exact rightIdeal_square_mem_hereditary h _ hh.isSelfAdjoint
    (principalRightIdeal_of_square_le h _ hh (by rwa [hs]))

omit [PartialOrder A] [StarOrderedRing A] in
lemma principalRightIdeal_le_of_mem {h a : A} (ha : a ∈ principalRightIdeal h) :
    principalRightIdeal a ≤ principalRightIdeal h := by
  intro x hx
  apply closure_minimal _ (Submodule.isClosed_topologicalClosure _) hx
  rintro _ ⟨b, rfl⟩
  exact principalRightIdeal_mul_mem h a b ha

omit [PartialOrder A] [StarOrderedRing A] in
lemma principalRightIdeal_smul_le (h : A) (c : ℝ) :
    principalRightIdeal (c•h) ≤ principalRightIdeal h := by
  intro x hx
  apply closure_minimal _ (Submodule.isClosed_topologicalClosure _) hx
  rintro _ ⟨b, rfl⟩
  exact Submodule.le_topologicalClosure _ ⟨c•b, by
    change h*(c•b) = (c•h)*b
    simp only [mul_smul_comm, smul_mul_assoc]⟩

lemma principalRightIdeal_of_square_le_smul (h a : A) (hh : 0 ≤ h)
    {c : ℝ} (hc : 0 ≤ c) (ha : a*star a ≤ c•h) : a ∈ principalRightIdeal h :=
  principalRightIdeal_smul_le h c (principalRightIdeal_of_square_le (c•h) a
    (smul_nonneg hc hh) ha)

lemma mem_hereditary_of_le_smul (h x : A) (hh : 0 ≤ h) (hx : 0 ≤ x)
    {c : ℝ} (hc : 0 ≤ c) (hxh : x ≤ c•h) :
    x ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  have hs : CFC.sqrt x * star (CFC.sqrt x) = x := by
    rw [(CFC.sqrt_nonneg x).star_eq, CFC.sqrt_mul_sqrt_self x hx]
  rw [← hs]
  exact rightIdeal_square_mem_hereditary h _ hh.isSelfAdjoint
    (principalRightIdeal_of_square_le_smul h _ hh hc (by rwa [hs]))

lemma principalRightIdeal_sqrt (h : A) (hh : 0 ≤ h) :
    principalRightIdeal (CFC.sqrt h) = principalRightIdeal h := by
  apply le_antisymm
  · apply principalRightIdeal_le_of_mem
    exact hereditary_le_rightIdeal h hh.isSelfAdjoint
      (sqrt_mem_hereditary h h hh.isSelfAdjoint (self_mem_hereditary h hh) hh)
  · apply principalRightIdeal_le_of_mem
    have hs : CFC.sqrt h*CFC.sqrt h ∈ principalRightIdeal (CFC.sqrt h) :=
      Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ (CFC.sqrt h))
    simpa only [CFC.sqrt_mul_sqrt_self h hh] using hs

lemma exists_exact_initial_square_of_domination (u d : A) (hd : 0 ≤ d)
    {c : ℝ} (hc : 0 ≤ c) (hdu : d ≤ c • (star u*u)) :
    ∃ r : A, star r*r = d ∧ r ∈ principalRightIdeal u := by
  let a := CFC.sqrt d
  have ha : a*star a = d := by
    dsimp only [a]
    rw [(CFC.sqrt_nonneg d).star_eq, CFC.sqrt_mul_sqrt_self d hd]
  have hamem : a ∈ principalRightIdeal (CFC.abs u) := by
    have hat := principalRightIdeal_of_square_le_smul (star u*u) a
      (star_mul_self_nonneg u) hc (by rwa [ha])
    rw [← principalRightIdeal_sqrt (star u*u) (star_mul_self_nonneg u)] at hat
    exact hat
  let a₀ : principalRightIdeal (CFC.abs u) := ⟨a, hamem⟩
  refine ⟨partialPolar u a₀, ?_, partialPolar_mem_rightIdeal u a₀⟩
  rw [partialPolar_initial_square]
  change star a*a = d
  rw [show star a = a from (CFC.sqrt_nonneg d).star_eq]
  rw [show a*a = d from CFC.sqrt_mul_sqrt_self d hd]

lemma exists_exact_initial_square_in_hereditary (h u d : A) (hh : 0 ≤ h)
    (hu : u ∈ principalRightIdeal h) (hd : 0 ≤ d) {c : ℝ} (hc : 0 ≤ c)
    (hdu : d ≤ c • (star u*u)) :
    ∃ r : A, star r*r = d ∧ r*star r ∈ hereditarySubalgebra h hh.isSelfAdjoint := by
  obtain ⟨r, hr, hrmem⟩ := exists_exact_initial_square_of_domination u d hd hc hdu
  exact ⟨r, hr, rightIdeal_square_mem_hereditary h r hh.isSelfAdjoint
    (principalRightIdeal_le_of_mem hu hrmem)⟩

lemma exists_comparison_of_rightIdeal (h a : A) (hh : 0 ≤ h)
    (ha : a ∈ principalRightIdeal h) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖star v*h*v - star a*a‖ < ε := by
  have ha' : a ∈ principalRightIdeal (CFC.sqrt h) := by
    rwa [principalRightIdeal_sqrt h hh]
  let F : Set A := closure (Set.range (fun v : A => star v*h*v))
  have hc : IsClosed {a : A | star a*a ∈ F} :=
    isClosed_closure.preimage (by fun_prop)
  have hamem : star a*a ∈ F := by
    apply closure_minimal _ hc ha'
    rintro _ ⟨v, rfl⟩
    apply subset_closure
    refine ⟨v, ?_⟩
    change star v*h*v = star (CFC.sqrt h*v)*(CFC.sqrt h*v)
    rw [star_mul, (CFC.sqrt_nonneg h).star_eq]
    calc
      star v*h*v = star v*(CFC.sqrt h*CFC.sqrt h)*v := by
        rw [CFC.sqrt_mul_sqrt_self h hh]
      _ = star v*CFC.sqrt h*(CFC.sqrt h*v) := by noncomm_ring
  obtain ⟨_, ⟨v, rfl⟩, hv⟩ := Metric.mem_closure_iff.mp hamem ε hε
  exact ⟨v, by simpa only [dist_eq_norm, norm_sub_rev] using hv⟩

lemma exists_comparison_of_hereditary (h x : A) (hh : 0 ≤ h) (hx : 0 ≤ x)
    (hmem : x ∈ hereditarySubalgebra h hh.isSelfAdjoint) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖star v*h*v-x‖ < ε := by
  have hs : star (CFC.sqrt x)*CFC.sqrt x = x := by
    rw [(CFC.sqrt_nonneg x).star_eq, CFC.sqrt_mul_sqrt_self x hx]
  have ha := hereditary_le_rightIdeal h hh.isSelfAdjoint
    (sqrt_mem_hereditary h x hh.isSelfAdjoint hmem hx)
  simpa only [hs] using exists_comparison_of_rightIdeal h (CFC.sqrt x) hh ha ε hε

lemma exists_comparison_of_star_mul (u : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : A, ‖star v*(u*star u)*v - star u*u‖ < ε :=
  exists_comparison_of_rightIdeal (u*star u) u (mul_star_self_nonneg u)
    (principalRightIdeal_of_square_le (u*star u) u (mul_star_self_nonneg u) le_rfl) ε hε

end

end WeakPureInfiniteness
end

end OAI
