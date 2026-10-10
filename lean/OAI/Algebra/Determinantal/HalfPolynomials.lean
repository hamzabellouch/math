import OAI.Algebra.Determinantal.FilteredPlane

namespace OAI

namespace PermanentBorder.LinearParameters
open Module
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {S ι κ : Type*} [AddCommGroup S] [Module L S] [Fintype ι] [Fintype κ]

theorem add_constrained_parameters (F : IntermediateField K L) (n : ℕ)
    (hF : Algebra.trdeg K F ≤ (n : Cardinal)) (c : Basis κ L S)
    (v : ι → S) (x : ι → L) (hvc : ∀ i j, c.repr (v i) j ∈ F)
    (hx : ∀ j, c.repr (∑ i, x i • v i) j ∈ F) :
    ∃ E : IntermediateField K L, F ≤ E ∧ (∀ i, x i ∈ E) ∧
      Algebra.trdeg K E ≤
        (n + (Fintype.card ι - finrank L (Submodule.span L (Set.range v))) : ℕ) := by
  classical
  let : Module.Finite L S := Module.Finite.of_basis c
  let r := finrank L (Submodule.span L (Set.range v))
  obtain ⟨w,hw,_,hwi⟩ := Submodule.exists_fun_fin_finrank_span_eq L (Set.range v)
  choose j hj using hw
  have hji : Function.Injective j := by
    intro a b h
    apply hwi.injective
    rw [← hj a,← hj b,h]
  let e := Equiv.ofInjective j hji
  let t := (Set.range j)ᶜ
  have ht : Fintype.card t = Fintype.card ι - r := by
    rw [Fintype.card_compl_set,← Fintype.card_congr e]
    simp only [Fintype.card_fin,r]
  obtain ⟨E,hFE,hxE,hE⟩ := SliceParameters.add_parameters F n hF (fun i : t => x i)
  have hsum : (∑ a, x (j a) • v (j a)) =
      (∑ i, x i • v i) - ∑ i : t, x i • v i := by
    have he := Equiv.sum_comp e (fun a : Set.range j => x a • v a)
    change (∑ a, x (j a) • v (j a)) = _ at he
    rw [he]
    apply eq_sub_of_add_eq
    convert Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ Set.range j)
      (fun i => x i • v i) using 1
    congr 3
    exact Subsingleton.elim _ _
  have hpi : LinearIndependent L (fun a => v (j a)) := by
    simpa only [hj] using hwi
  have hpE : ∀ a, x (j a) ∈ E := independent_coefficients_mem E c
      (fun a => v (j a)) hpi (fun a => x (j a))
      (fun a k => hFE (hvc (j a) k)) (by
        intro k
        rw [hsum,map_sub]
        apply E.sub_mem (hFE (hx k))
        simp only [map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
        exact E.sum_mem (fun i _ => E.mul_mem (hxE i) (hFE (hvc i k))))
  refine ⟨E,hFE,?_,?_⟩
  · intro i
    by_cases hi : i ∈ Set.range j
    · obtain ⟨a,rfl⟩ := hi
      exact hpE a
    · exact hxE ⟨i,hi⟩
  · simpa only [ht] using hE

end PermanentBorder.LinearParameters
namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

def InField (F : IntermediateField K L) (p : MvPolynomial (Fin 2) L) : Prop :=
  ∀ s, p.coeff s ∈ F

lemma inField_lift (F : IntermediateField K L) {p : MvPolynomial (Fin 2) L}
    (hp : InField F p) : ∃ p₀ : MvPolynomial (Fin 2) F, p₀.map F.val.toRingHom = p := by
  apply mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨s,_,rfl⟩ := mem_coeffs_iff.mp hc
  exact ⟨⟨_,hp s⟩,rfl⟩

lemma inField_of_high {F : IntermediateField K L} {p : MvPolynomial (Fin 2) L}
    {B : ℕ} (hp : ∀ s, B ≤ s.degree → p.coeff s ∈ F)
    (hlow : ∀ s : Index B, p.coeff s.val ∈ F) : InField F p := by
  intro s
  by_cases hs : s.degree < B
  · exact hlow ⟨s,hs⟩
  · exact hp s (by omega)

lemma span_low (q : MvPolynomial (Fin 2) L →ₐ[L] R) (B : ℕ) :
    Submodule.span L (Set.range (fun s : Index B => q (monomial s.val (1 : L)))) = filtered q B := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    cases B with
    | zero => exact False.elim (Nat.not_lt_zero _ s.property)
    | succ B =>
      apply (mem_filtered_succ q B _).mpr
      refine ⟨_,(totalDegree_monomial_le _ _).trans ?_,rfl⟩
      change s.val.degree ≤ B
      have h:=s.property
      omega
  · cases B with
    | zero => exact bot_le
    | succ B =>
      intro z hz
      obtain ⟨p,hp,rfl⟩ := (mem_filtered_succ q B z).mp hz
      rw [LowPlane.expansion (B := B+1) p (by
        intro s hs
        have hc : s.degree ≤ p.totalDegree := le_totalDegree hs
        omega),map_sum]
      apply Submodule.sum_mem
      intro s _
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self s))

lemma repr_polynomial_mem {ι : Type*} [Fintype ι] (F : IntermediateField K L)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (c : Basis ι L R)
    (hmon : ∀ s i, c.repr (q (monomial s (1 : L))) i ∈ F)
    (p : MvPolynomial (Fin 2) L) (hp : InField F p) :
    ∀ i, c.repr (q p) i ∈ F := by
  classical
  intro i
  rw [p.as_sum]
  simp only [map_sum,Finsupp.finsetSum_apply]
  apply F.sum_mem
  intro s _
  have he : monomial s (p.coeff s) = p.coeff s • monomial s (1 : L) := by rw [smul_monomial,smul_eq_mul,mul_one]
  rw [he,map_smul,map_smul,Finsupp.smul_apply,smul_eq_mul]
  exact F.mul_mem (hp s) (hmon s i)

theorem add_vanishing_polynomial {ι : Type*} [Fintype ι]
    (F : IntermediateField K L) (n B : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (c : Basis ι L R)
    (hmon : ∀ s i, c.repr (q (monomial s (1 : L))) i ∈ F)
    (p t : MvPolynomial (Fin 2) L) (ht : InField F t)
    (hhigh : ∀ s, B ≤ s.degree → p.coeff s = t.coeff s) (hpq : q p = 0) :
    ∃ E : IntermediateField K L, F ≤ E ∧ InField E p ∧
      Algebra.trdeg K E ≤ (n + (Fintype.card (Index B) - finrank L (filtered q B)) : ℕ) := by
  classical
  have he := remainder_expansion p t hhigh
  have hsum : ∑ s : Index B, (p-t).coeff s.val • q (monomial s.val 1) = -q t := by
    have hh := congrArg q he
    rw [hpq,map_add,map_sum] at hh
    simp only [map_smul] at hh
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hh.symm)
  obtain ⟨E,hFE,hxE,hE⟩ := LinearParameters.add_constrained_parameters F n hF c
    (fun s : Index B => q (monomial s.val 1)) (fun s => (p-t).coeff s.val)
    (fun s i => hmon s.val i) (by
      intro i
      rw [hsum,map_neg]
      exact F.neg_mem (repr_polynomial_mem F q c hmon t ht i))
  refine ⟨E,hFE,?_,?_⟩
  · intro s
    by_cases hs : s.degree < B
    · have hh := hxE ⟨s,hs⟩
      rw [coeff_sub] at hh
      have ht' := hFE (ht s)
      simpa only [sub_add_cancel] using E.add_mem hh ht'
    · rw [hhigh s (by omega)]
      exact hFE (ht s)
  · rwa [span_low] at hE

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

lemma adjoin_polynomial (F : IntermediateField K L) (n B : ℕ)
    (hF : Algebra.trdeg K F ≤ (n : Cardinal)) (p : MvPolynomial (Fin 2) L)
    (hhigh : ∀ s, B ≤ s.degree → p.coeff s ∈ F) :
    ∃ E : IntermediateField K L, F ≤ E ∧ InField E p ∧
      Algebra.trdeg K E ≤ (n + Fintype.card (Index B) : ℕ) := by
  obtain ⟨E,hFE,hc,hE⟩ := SliceParameters.add_parameters F n hF
    (fun s : Index B => p.coeff s.val)
  exact ⟨E,hFE,inField_of_high (fun s hs => hFE (hhigh s hs)) hc,hE⟩

lemma monomial_plane (s : Fin 2 →₀ ℕ) :
    (monomial s 1 : MvPolynomial (Fin 2) L) = X 0 ^ s 0 * X 1 ^ s 1 := by
  rw [monomial_eq,C_1,one_mul,Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_two]

theorem extend_by_quotient [Infinite K] [IsAlgClosed L] [Module.Finite L R]
    (F : IntermediateField K L) (n : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (p : MvPolynomial (Fin 2) L) (hp : p ≠ 0) (hpF : InField F p)
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (hq : Function.Surjective q) (hpq : q p = 0)
    (c : Basis (Fin (finrank L R)) L R) (a b : Fin (finrank L R) → ℕ)
    (hc : ∀ i, c i=q (X 0 ^ a i * X 1 ^ b i)) :
    ∃ E : IntermediateField K L, F ≤ E ∧
      (∀ s i, c.repr (q (monomial s (1 : L))) i ∈ E) ∧
      Algebra.trdeg K E ≤ (n + finrank L R : ℕ) := by
  obtain ⟨p₀,hp₀⟩ := inField_lift F hpF
  have hp0 : p₀ ≠ 0 := by intro hz; apply hp; rw [← hp₀,hz,map_zero]
  let : Infinite F := Infinite.of_injective (algebraMap K F) (algebraMap K F).injective
  obtain ⟨E,hE,hA,hB,hv⟩ := CurveQuotientParameters.chart_field_bound p₀ hp0 q hq
    (by change q (p₀.map F.val.toRingHom)=0; rw [hp₀,hpq]) c a b hc
  let : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).mpr
    (algebraMap F E).injective
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨E.restrictScalars K,?_,?_,?_⟩
  · intro x hx
    exact E.algebraMap_mem ⟨x,hx⟩
  · intro s i
    rw [monomial_plane]
    exact FinitePlaneFrames.monomial_coordinates_mem E q c hA hB hv (s 0) (s 1) i
  · change Algebra.trdeg K E ≤ _
    rw [← trdeg_add_eq K F]
    exact (add_le_add hF hE).trans_eq (by simp)

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

lemma filtered_rank_le (q : MvPolynomial (Fin 2) L →ₐ[L] R) (B : ℕ) :
    finrank L (filtered q B) ≤ Fintype.card (Index B) := by
  rw [← span_low]
  exact finrank_range_le_card _

lemma inField_map (F : IntermediateField K L) (p : MvPolynomial (Fin 2) K) :
    InField F (p.map (algebraMap K L)) := by
  intro s
  rw [coeff_map]
  exact F.algebraMap_mem _

lemma inField_mono {F E : IntermediateField K L} (hFE : F ≤ E)
    {p : MvPolynomial (Fin 2) L} (hp : InField F p) : InField E p := fun s => hFE (hp s)

theorem add_vanishing_family {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : IntermediateField K L) (n : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (c : Basis ι L R)
    (hmon : ∀ s i, c.repr (q (monomial s (1 : L))) i ∈ F)
    (B : κ → ℕ) (p : κ → MvPolynomial (Fin 2) L) (t : κ → MvPolynomial (Fin 2) K)
    (hhigh : ∀ i s, B i ≤ s.degree → (p i).coeff s = algebraMap K L ((t i).coeff s))
    (hpq : ∀ i, q (p i) = 0) (U : Finset κ) :
    ∃ E : IntermediateField K L, F ≤ E ∧ (∀ i ∈ U, InField E (p i)) ∧
      Algebra.trdeg K E ≤ (n + ∑ i ∈ U, (Fintype.card (Index (B i)) - finrank L (filtered q (B i))) : ℕ) := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨F,le_rfl,by simp,by simpa using hF⟩
  | @insert i U hi ih =>
    obtain ⟨E,hFE,hpE,hE⟩ := ih
    obtain ⟨D,hED,hpD,hD⟩ := add_vanishing_polynomial E _ (B i) hE q c
      (fun s j => hFE (hmon s j)) (p i) ((t i).map (algebraMap K L)) (inField_map E _)
      (by intro s hs; rw [coeff_map]; exact hhigh i s hs) (hpq i)
    refine ⟨D,hFE.trans hED,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact hpD
      · exact inField_mono hED (hpE j hj)
    · simpa only [Finset.sum_insert hi,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hD

theorem four_polynomial_bound [Infinite K] [IsAlgClosed L] [Module.Finite L R]
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (hq : Function.Surjective q)
    (B₀ : ℕ) (B : Fin 3 → ℕ)
    (p₀ : MvPolynomial (Fin 2) L) (p : Fin 3 → MvPolynomial (Fin 2) L)
    (t₀ : MvPolynomial (Fin 2) K) (t : Fin 3 → MvPolynomial (Fin 2) K)
    (hp₀ : p₀ ≠ 0) (h₀ : ∀ s, B₀ ≤ s.degree → p₀.coeff s=algebraMap K L (t₀.coeff s))
    (h : ∀ i s, B i ≤ s.degree → (p i).coeff s=algebraMap K L ((t i).coeff s))
    (hq₀ : q p₀=0) (hqp : ∀ i, q (p i)=0)
    (hrank : ∀ i, finrank L R ≤ 2*finrank L (filtered q (B i))) :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E p₀ ∧ (∀ i, InField E (p i)) ∧
      Algebra.trdeg K E ≤ (n : Cardinal) ∧
      2*n + finrank L R ≤ 2*(Fintype.card (Index B₀) + ∑ i, Fintype.card (Index (B i))) := by
  classical
  have hbot : Algebra.trdeg K (⊥ : IntermediateField K L) ≤ (0 : Cardinal) := by rw [trdeg_eq_zero]
  obtain ⟨F,_,hpF,hF⟩ := adjoin_polynomial (⊥ : IntermediateField K L) 0 B₀ hbot p₀
    (by intro s hs; rw [h₀ s hs]; exact IntermediateField.algebraMap_mem _ _)
  obtain ⟨c,a,b,hc⟩ := FinitePlaneFrames.exists_monomial_basis q hq
  obtain ⟨D,hFD,hmon,hD⟩ := extend_by_quotient F _ hF p₀ hp₀ hpF q hq hq₀ c a b hc
  obtain ⟨E,hDE,hpE,hE⟩ := add_vanishing_family D _ hD q c hmon B p t h hqp Finset.univ
  refine ⟨E,_,inField_mono (hFD.trans hDE) hpF,(fun i => hpE i (Finset.mem_univ i)),hE,?_⟩
  let N := fun i => Fintype.card (Index (B i))
  let r := fun i => finrank L (filtered q (B i))
  have hle (i) : r i ≤ N i := filtered_rank_le q (B i)
  have he : ∑ i, (N i-r i) + ∑ i, r i = ∑ i, N i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel (hle i)
  have hh : 3*finrank L R ≤ 2*∑ i, r i := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrank i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,← Finset.mul_sum] using hs
  change 2*(0+Fintype.card (Index B₀)+finrank L R+∑ i, (N i-r i))+finrank L R ≤ 2*(Fintype.card (Index B₀)+∑ i, N i)
  omega

end PermanentBorder.CurveFamily

namespace PermanentBorder.FrobeniusPlane
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [CharP L 2]

lemma derivation_square {M : Type*} [AddCommGroup M] [Module K M]
    [Module L M] [IsScalarTower K L M] (D : Derivation K L M) (a : L) :
    D (a^2) = 0 := by
  rw [D.leibniz_pow,← Nat.cast_smul_eq_nsmul L]
  simp only [CharP.cast_eq_zero L 2,zero_smul]

omit [CharP L 2] in
lemma derivation_zero_of_field_generators {M : Type*} [AddCommGroup M] [Module K M]
    [Module L M] [IsScalarTower K L M] (D : Derivation K L M)
    (s : Set L) (hs : IntermediateField.adjoin K s = ⊤) (hD : ∀ x ∈ s, D x = 0) : D = 0 := by
  let F : IntermediateField K L :=
    { carrier := {x | D x = 0}
      zero_mem' := map_zero D
      one_mem' := D.map_one_eq_zero
      add_mem' := by
        intro x y hx hy
        change D x = 0 at hx
        change D y = 0 at hy
        change D (x+y) = 0
        rw [map_add,hx,hy,add_zero]
      mul_mem' := by
        intro x y hx hy
        change D x = 0 at hx
        change D y = 0 at hy
        change D (x*y) = 0
        rw [D.leibniz,hx,hy,smul_zero,smul_zero,add_zero]
      inv_mem' := by
        intro x hx
        change D x = 0 at hx
        change D x⁻¹ = 0
        rw [D.leibniz_inv,hx,smul_zero]
      algebraMap_mem' := fun r => D.map_algebraMap r }
  have hF : IntermediateField.adjoin K s ≤ F := IntermediateField.adjoin_le_iff.mpr hD
  rw [hs] at hF
  ext x
  exact hF (show x ∈ (⊤ : IntermediateField K L) from trivial)

theorem finite_of_square_coordinate_equations (x : Fin 2 → L)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤)
    (b c d : L) (hd : d ≠ 0)
    (hb : b^2+x 1*d^2=0) (hc : c^2+x 0*d^2=0) : Module.Finite K L := by
  classical
  let D := KaehlerDifferential.D K L
  have hx (i : Fin 2) : D (x i) = 0 := by
    have h (v a : L) (he : a^2+v*d^2=0) : D v = 0 := by
      have hh := congrArg D he
      simp only [map_add,D.leibniz,derivation_square,smul_zero,zero_add,map_zero] at hh
      exact (smul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 hd)
    fin_cases i
    · exact h _ _ hc
    · exact h _ _ hb
  have hD : D = 0 := derivation_zero_of_field_generators D _ hgen (by
    rintro _ ⟨i,rfl⟩; exact hx i)
  have hbot : (⊤ : Submodule L (KaehlerDifferential K L)) ≤ ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation,Submodule.span_le]
    rintro _ ⟨a,rfl⟩
    change D a = 0
    rw [hD]; rfl
  let : Algebra.FormallyUnramified K L := ⟨(subsingleton_iff_forall_eq 0).mpr (fun a => hbot trivial)⟩
  let : Algebra.EssFiniteType K L := IntermediateField.fg_top_iff.mp
    ⟨Finset.univ.image x,by simpa using hgen⟩
  exact Algebra.FormallyUnramified.finite_of_free K L
end PermanentBorder.FrobeniusPlane
namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

theorem node_coordinates_algebraic (x : Fin 2 → L)
    (b c d : MvPolynomial (Fin 2) K) (hd : aeval x d ≠ 0)
    (hb : (aeval x b)^2+x 1*(aeval x d)^2=0)
    (hc : (aeval x c)^2+x 0*(aeval x d)^2=0) : ∀ i, IsAlgebraic K (x i) := by
  let E := IntermediateField.adjoin K (Set.range x)
  let y : Fin 2 → E := fun i => ⟨x i,IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  have hgen : IntermediateField.adjoin K (Set.range y) = ⊤ := by
    apply IntermediateField.map_injective E.val
    rw [IntermediateField.adjoin_map,← Set.range_comp,← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    rfl
  let : CharP E 2 := (algebraMap E L).charP (algebraMap E L).injective 2
  have he (p : MvPolynomial (Fin 2) K) : E.val.toRingHom (aeval y p) = aeval x p := by
    change E.val (aeval y p) = _
    rw [← AlgHom.comp_apply]
    congr 1
    ext i
    simp [y]
  have hy (i) : E.val.toRingHom (y i) = x i := rfl
  let : Module.Finite K E := finite_of_square_coordinate_equations y hgen
    (aeval y b) (aeval y c) (aeval y d) (by intro hz; apply hd; rw [← he d,hz,map_zero])
    (by apply E.val.injective; simpa only [map_add,map_mul,map_pow,AlgHom.coe_toRingHom,he,hy,map_zero] using hb)
    (by apply E.val.injective; simpa only [map_add,map_mul,map_pow,AlgHom.coe_toRingHom,he,hy,map_zero] using hc)
  intro i
  exact (IsAlgebraic.of_finite K (y i)).algHom E.val

end PermanentBorder.FrobeniusPlane

end OAI
