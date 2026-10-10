import OAI.Analysis.CStarAlgebra.PureInfiniteness.PositiveFunctional
import OAI.Analysis.CStarAlgebra.PureInfiniteness.Separation

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def compressedPositive (f : A →ₚ[ℂ] ℂ) (u : A) : A →ₚ[ℂ] ℂ where
  toFun a := f (star u * a * u)
  map_add' a b := by simp only [mul_add, add_mul, map_add]
  map_smul' c a := by simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply]
  monotone' := fun _ _ hab => f.monotone (star_left_conjugate_le_conjugate hab _)

lemma compressedPositive_norm (f : A →ₚ[ℂ] ℂ) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    {u : A} (hu : ‖u‖ ≤ 1) (a : A) : ‖compressedPositive f u a‖ ≤ ‖a‖ := by
  calc
    ‖compressedPositive f u a‖ ≤ ‖star u * a * u‖ := hf _
    _ ≤ ‖u‖ * ‖a‖ * ‖u‖ := by
      grw [norm_mul_le, norm_mul_le, norm_star]
    _ ≤ 1 * ‖a‖ * 1 := by gcongr
    _ = ‖a‖ := by ring

lemma compressedPositive_square (f : A →ₚ[ℂ] ℂ) (u a : A) :
    compressedPositive f u (star a * a) = f (star (a * u) * (a * u)) := by
  change f (star u * (star a * a) * u) = _
  simp only [star_mul, mul_assoc]

lemma norm_one_sub_positive_contraction {e : A} (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) :
    ‖1 - e‖ ≤ 1 := by
  have he1 : e ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg e he).mp hen
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (1 - e) (sub_nonneg.mpr he1)).mpr
    (sub_le_self _ he)

lemma exists_rep_killing_ideal (J : NonUnitalStarSubalgebra ℂ A)
    (hJ : IsClosed (J : Set A))
    (hleft : ∀ a : A, ∀ z ∈ J, a * z ∈ J)
    (hright : ∀ a : A, ∀ z ∈ J, z * a ∈ J)
    {a : A} (ha : a ∉ J) :
    ∃ R : HilbertRep.{u,u} A, (∀ z ∈ J, R.hom z = 0) ∧ R.hom a ≠ 0 := by
  classical
  have : Nontrivial A := ⟨⟨a, 0, fun h => ha (h.symm ▸ J.zero_mem)⟩⟩
  have : CompleteSpace J := hJ.completeSpace_coe
  let : PartialOrder J := CStarAlgebra.spectralOrder J
  let : StarOrderedRing J := CStarAlgebra.spectralOrderedRing J
  have hau := CStarAlgebra.increasingApproximateUnit J
  let I := {e : J // @LE.le J (CStarAlgebra.spectralOrder J).toLE 0 e ∧ ‖e‖ ≤ 1}
  let F : Filter I := Filter.comap Subtype.val (CStarAlgebra.approximateUnit J)
  have : F.NeBot := Filter.NeBot.comap_of_range_mem inferInstance (by
    filter_upwards [hau.eventually_nonneg.and hau.eventually_norm] with e he
    exact ⟨⟨e, he⟩, rfl⟩)
  let ω := Ultrafilter.of F
  have hω : (ω : Filter I) ≤ F := Ultrafilter.of_le F
  have hunit (z : J) : Tendsto (fun e : I => (z : A) * (1 - (e.val : A)))
      (ω : Filter I) (𝓝 0) := by
    have hh := (continuous_subtype_val.tendsto z).comp
      (hau.tendsto_mul_left z |>.comp (Filter.tendsto_comap.mono_left hω))
    have hz := (tendsto_const_nhds (x := (z : A))).sub hh
    convert hz using 1 <;> simp only [mul_sub, mul_one, sub_self]
    rfl
  have hadef : a ∉ closure (J : Set A) := by rwa [hJ.closure_eq]
  rw [Metric.mem_closure_iff] at hadef
  push Not at hadef
  obtain ⟨r, hr, hdist⟩ := hadef
  have hlower (e : I) : r ≤ ‖a * (1 - (e.val : A))‖ := by
    have hh := hdist (a * (e.val : A)) (hleft a _ e.val.property)
    simpa only [dist_eq_norm, mul_sub, mul_one] using hh
  have hen (e : I) : ‖1 - (e.val : A)‖ ≤ 1 := by
    apply norm_one_sub_positive_contraction
    · obtain ⟨b, hb⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp e.property.1
      have hm := congrArg (fun z : J => (z : A)) hb
      change (e.val : A) = star (b : A) * (b : A) at hm
      rw [hm]
      exact star_mul_self_nonneg _
    · exact e.property.2
  have hex (e : I) := exists_norming_positive (A := A)
    (star_mul_self_nonneg (a * (1 - (e.val : A))))
  choose f hf hfa using hex
  let g (e : I) := compressedPositive (f e) (1 - (e.val : A))
  have hg (e : I) (z : A) : ‖g e z‖ ≤ ‖z‖ := compressedPositive_norm (f e) (hf e) (hen e) z
  let L := ultraPositive ω g hg
  have hL (z : A) (hz : z ∈ J) : L.gnsStarAlgHom z = 0 := by
    change L.gnsNonUnitalStarAlgHom z = 0
    apply gns_zero_of_sandwich
    intro b
    apply ultraPositive_eq_zero_of_tendsto
    have hlim := (hunit ⟨z * b, hright b z hz⟩).norm
    apply squeeze_zero_norm (fun e => ?_) (by simpa only [norm_zero, mul_zero] using hlim.mul hlim)
    calc
      ‖g e (star (z * b) * (z * b))‖ =
          ‖f e (star ((z * b) * (1 - (e.val : A))) * ((z * b) * (1 - (e.val : A))))‖ := by
        change ‖compressedPositive (f e) (1 - (e.val : A)) (star (z * b) * (z * b))‖ = _
        rw [compressedPositive_square]
      _ ≤ ‖star ((z * b) * (1 - (e.val : A))) * ((z * b) * (1 - (e.val : A)))‖ := hf e _
      _ = _ := CStarRing.norm_star_mul_self
  have hnon : L (star a * a) ≠ 0 := by
    have hv (e : I) : g e (star a * a) = (‖a * (1 - (e.val : A))‖ ^ 2 : ℝ) := by
      change compressedPositive (f e) (1 - (e.val : A)) (star a * a) = _
      rw [compressedPositive_square, hfa e, CStarRing.norm_star_mul_self, pow_two]
    have hb : (r ^ 2 : ℂ) ≤ L (star a * a) :=
      ge_of_tendsto' (tendsto_ultraPositive ω g hg _) (fun e => by
        rw [hv e]
        exact_mod_cast pow_le_pow_left₀ hr.le (hlower e) 2)
    intro heq
    rw [heq] at hb
    have : r ^ 2 ≤ 0 := by exact_mod_cast hb
    nlinarith
  exact ⟨⟨L.GNS, L.gnsStarAlgHom⟩, hL, gnsStar_nonzero_of_value L a hnon⟩
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance idealDetectionOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance idealDetectionStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

def ScalarCuntzLE (u v : A) : Prop :=
  u ∈ closure (Set.range (fun w : A => star w * v * w))

lemma scalarCuntzLE_iff_finite (u v : A) :
    ScalarCuntzLE u v ↔ FiniteCuntzLE (scalarCorner u) (scalarCorner v) := by
  let E : A ≃⋆ₐ[ℂ] CStarMatrix (Fin 1) (Fin 1) A :=
    CStarMatrix.toOneByOne (Fin 1) ℂ A
  have hc : Continuous E := (StarAlgEquiv.isometry E).continuous
  have hci : Continuous E.symm := (StarAlgEquiv.isometry E.symm).continuous
  rw [finiteCuntzLE_iff_closure]
  change u ∈ closure (Set.range (fun w : A => star w * v * w)) ↔
    E u ∈ closure (Set.range (fun w : CStarMatrix (Fin 1) (Fin 1) A =>
      star w * E v * w))
  constructor
  · intro h
    apply closure_mono (s := E '' Set.range (fun w : A => star w * v * w)) _
      (image_closure_subset_closure_image hc ⟨u, h, rfl⟩)
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨E w, by simp [map_star]⟩
  · intro h
    have hh := image_closure_subset_closure_image hci ⟨E u, h, rfl⟩
    simp only [StarAlgEquiv.symm_apply_apply] at hh
    apply closure_mono (s := E.symm '' Set.range (fun w => star w * E v * w)) _ hh
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨E.symm w, by simp [map_star]⟩

lemma ScalarCuntzLE.exists_approx {u v : A} (h : ScalarCuntzLE u v)
    {ε : ℝ} (hε : 0 < ε) : ∃ w : A, ‖star w * v * w - u‖ < ε := by
  obtain ⟨_, ⟨w, rfl⟩, hw⟩ := Metric.mem_closure_iff.mp h ε hε
  exact ⟨w, by simpa only [dist_eq_norm, norm_sub_rev] using hw⟩

lemma ScalarCuntzLE.trans {u v w : A} (h : ScalarCuntzLE u v)
    (h' : ScalarCuntzLE v w) : ScalarCuntzLE u w :=
  (scalarCuntzLE_iff_finite _ _).mpr
    (((scalarCuntzLE_iff_finite _ _).mp h).trans ((scalarCuntzLE_iff_finite _ _).mp h'))

lemma scalarCuntzLE_of_mem_Her {u v : A} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : u ∈ Her v) : ScalarCuntzLE u v := by
  have hs := sqrt_mem_Her h hu
  have hc : Continuous (fun z : A => star z * z) := by fun_prop
  have hm := image_closure_subset_closure_image hc ⟨CFC.sqrt u, hs, rfl⟩
  simp only [(CFC.sqrt_nonneg u).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self u hu] at hm
  apply closure_mono (s := (fun z : A => star z * z) ''
      Set.range (fun w : A => v * w * star v)) _ hm
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  refine ⟨CFC.sqrt v * w * v, ?_⟩
  have hsv := (CFC.sqrt_nonneg v).isSelfAdjoint.star_eq
  have hsq := CFC.sqrt_mul_sqrt_self v hv
  simp only [star_mul, hv.isSelfAdjoint.star_eq, hsv, mul_assoc]
  have hh : CFC.sqrt v * v * CFC.sqrt v = v * v := by
    calc
      _ = CFC.sqrt v * (CFC.sqrt v * CFC.sqrt v) * CFC.sqrt v :=
        congrArg (fun t => CFC.sqrt v * t * CFC.sqrt v) hsq.symm
      _ = (CFC.sqrt v * CFC.sqrt v) * (CFC.sqrt v * CFC.sqrt v) := by noncomm_ring
      _ = v * v := by rw [hsq]
  calc
    _ = v * star w * (CFC.sqrt v * v * CFC.sqrt v) * w * v := by noncomm_ring
    _ = _ := by rw [hh]; noncomm_ring

lemma scalarCuntzLE_of_order {u v : A} (hu : 0 ≤ u) (h : u ≤ v) :
    ScalarCuntzLE u v := scalarCuntzLE_of_mem_Her hu (hu.trans h) (mem_Her_of_nonneg_le hu h)

lemma scalarCuntzLE_smul {v : A} (hv : 0 ≤ v) {K : ℝ} (hK : 0 < K) :
    ScalarCuntzLE (K • v) v := by
  apply scalarCuntzLE_of_mem_Her (smul_nonneg hK.le hv) hv
  exact real_smul_mem_Her (self_mem_Her hv) K

end MainGap

end

end OAI
