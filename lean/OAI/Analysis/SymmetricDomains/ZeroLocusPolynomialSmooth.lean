import Mathlib
import OAI.Analysis.SymmetricDomains.AmbientInverse

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem finite_analytic_sheets_chart {n d : ℕ} {K : Type*} [Finite K]
    (V : Set (Affine n)) (π : Affine n → Affine d)
    (hπ : AnalyticOnNhd ℂ π univ)
    {A : Set (Affine d)} (hA : IsOpen A)
    (g : K → Affine d → Affine n) (hg : ∀ i, AnalyticOnNhd ℂ (g i) A)
    (hsheets : ∀ y ∈ A, Function.Injective (fun i => g i y) ∧
      ∀ z, z ∈ V ∧ π z = y ↔ ∃ i, g i y = z)
    {q : Affine n} (hq : q ∈ V) (hqa : π q ∈ A) :
    ∃ W : Set (Affine n), W ⊆ V ∧ IsOpen ((Subtype.val : V → Affine n) ⁻¹' W) ∧ q ∈ W ∧
      ∃ D : Set (Affine d), IsOpen D ∧ Nonempty (Biholomorph W D) := by
  obtain ⟨i,hi⟩ := (hsheets (π q) hqa).2 q |>.mp ⟨hq,rfl⟩
  obtain ⟨O,hO,hqO,B,hB,haB,hiso⟩ := finite_sheet_isolating_neighborhood g
    (fun j => (hg j (π q) hqa).continuousAt) (hsheets (π q) hqa).1 i
  let D := B ∩ A
  have hD : IsOpen D := hB.inter hA
  let W := V ∩ π ⁻¹' D ∩ O
  have hWV : W ⊆ V := fun _ hx => hx.1.1
  have hWo : IsOpen ((Subtype.val : V → Affine n) ⁻¹' W) := by
    have he : (Subtype.val : V → Affine n) ⁻¹' W =
        (fun x : V => π x.val) ⁻¹' D ∩ (Subtype.val : V → Affine n) ⁻¹' O := by
      ext x
      simp only [W, mem_preimage, mem_inter_iff, x.property, true_and]
    rw [he]
    exact (hD.preimage (hπ.continuous.comp continuous_subtype_val)).inter
      (hO.preimage continuous_subtype_val)
  have hqW : q ∈ W := ⟨⟨hq,⟨haB,hqa⟩⟩,hi ▸ hqO⟩
  have hgy : ∀ y ∈ D, g i y ∈ V ∧ π (g i y) = y := by
    intro y hy
    exact (hsheets y hy.2).2 (g i y) |>.mpr ⟨i,rfl⟩
  have hgW : MapsTo (g i) D W := by
    intro y hy
    exact ⟨⟨(hgy y hy).1, by change π (g i y) ∈ D; rw [(hgy y hy).2]; exact hy⟩,
      (hiso y hy.1 i).mpr rfl⟩
  have hgπ : ∀ z ∈ W, g i (π z) = z := by
    intro z hz
    obtain ⟨j,hj⟩ := (hsheets (π z) hz.1.2.2).2 z |>.mp ⟨hz.1.1,rfl⟩
    have hji : j = i := (hiso (π z) hz.1.2.1 j).mp (by rw [hj]; exact hz.2)
    simpa only [hji] using hj
  exact ⟨W,hWV,hWo,hqW,D,hD,⟨biholomorphOfAmbientInverse W D π (g i)
    (hπ.mono (subset_univ _)) ((hg i).mono inter_subset_right)
    (fun _ hz => hz.1.2) hgW hgπ (fun y hy => (hgy y hy).2)⟩⟩

namespace Biholomorph

noncomputable def restrict {n m : ℕ} {S S' : Set (Affine n)} {T T' : Set (Affine m)}
    (e : Biholomorph S T) (hS : S' ⊆ S) (hT : T' ⊆ T)
    (he : ∀ x : S, x.val ∈ S' ↔ (e.toHomeomorph x).val ∈ T') :
    Biholomorph S' T' := by
  let F : S' → T' := fun x => ⟨(e.toHomeomorph (Set.inclusion hS x)).val,
    (he (Set.inclusion hS x)).mp x.property⟩
  let G : T' → S' := fun y => ⟨(e.toHomeomorph.symm (Set.inclusion hT y)).val,
    (he (e.toHomeomorph.symm (Set.inclusion hT y))).mpr (by
      simpa only [Homeomorph.apply_symm_apply] using y.property)⟩
  have hF : Continuous F :=
    (continuous_subtype_val.comp (e.toHomeomorph.continuous.comp
      (Topology.IsEmbedding.inclusion hS).continuous)).subtype_mk _
  have hG : Continuous G :=
    (continuous_subtype_val.comp (e.toHomeomorph.symm.continuous.comp
      (Topology.IsEmbedding.inclusion hT).continuous)).subtype_mk _
  refine ⟨⟨⟨F,G,?_,?_⟩,hF,hG⟩,?_,?_⟩
  · intro x
    apply Subtype.ext
    exact congrArg (Subtype.val : S → Affine n) (e.toHomeomorph.symm_apply_apply (Set.inclusion hS x))
  · intro y
    apply Subtype.ext
    exact congrArg (Subtype.val : T → Affine m) (e.toHomeomorph.apply_symm_apply (Set.inclusion hT y))
  · exact e.holomorphic_toFun.comp (f := Set.inclusion hS) (holomorphicOnSubset_val S')
  · exact e.holomorphic_invFun.comp (f := Set.inclusion hT) (holomorphicOnSubset_val T')

end Biholomorph

def SmoothAtSubset {n : ℕ} (S : Set (Affine n)) (q : Affine n) : Prop :=
  ∃ (m : ℕ) (W : Set (Affine n)), W ⊆ S ∧
    IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ q ∈ W ∧
    ∃ D : Set (Affine m), IsOpen D ∧ Nonempty (Biholomorph W D)

theorem smoothAtSubset_restrict_open {n : ℕ} {S T : Set (Affine n)}
    (hST : S ⊆ T) (hS : IsOpen ((Subtype.val : T → Affine n) ⁻¹' S))
    {q : Affine n} (hq : q ∈ S) (hqT : SmoothAtSubset T q) : SmoothAtSubset S q := by
  classical
  obtain ⟨m,W,hWT,hW,hqW,D,hD,⟨e⟩⟩ := hqT
  let Z : Set W := (Subtype.val : W → Affine n) ⁻¹' S
  have hZ : IsOpen Z := hS.preimage (Topology.IsEmbedding.inclusion hWT).continuous
  let D' := (Subtype.val : D → Affine m) '' (e.toHomeomorph '' Z)
  have hD' : IsOpen D' := hD.isOpenMap_subtype_val _ (e.toHomeomorph.isOpenMap _ hZ)
  have hD'D : D' ⊆ D := by rintro y ⟨z,_,rfl⟩; exact z.property
  have he : ∀ x : W, x.val ∈ W ∩ S ↔ (e.toHomeomorph x).val ∈ D' := by
    intro x
    constructor
    · intro hx
      exact ⟨e.toHomeomorph x,⟨x,hx.2,rfl⟩,rfl⟩
    · rintro ⟨y,⟨z,hz,hzy⟩,hy⟩
      have hzx : z = x := e.toHomeomorph.injective (hzy.trans (Subtype.ext hy))
      exact ⟨x.property,hzx ▸ hz⟩
  have hW' : IsOpen ((Subtype.val : S → Affine n) ⁻¹' (W ∩ S)) := by
    have hpre := hW.preimage (Topology.IsEmbedding.inclusion hST).continuous
    have heq : (Subtype.val : S → Affine n) ⁻¹' (W ∩ S) =
        Set.inclusion hST ⁻¹' ((Subtype.val : T → Affine n) ⁻¹' W) := by
      ext x
      simp only [mem_preimage, mem_inter_iff, x.property, and_true, Set.inclusion]
    rw [heq]
    exact hpre
  exact ⟨m,W ∩ S,inter_subset_right,hW',⟨hqW,hq⟩,D',hD',
    ⟨e.restrict inter_subset_left hD'D he⟩⟩

theorem Biholomorph.smoothAt_pullback {n m : ℕ} {S : Set (Affine n)} {T : Set (Affine m)}
    (e : Biholomorph S T) (q : S) (hq : SmoothAtSubset T (e.toHomeomorph q).val) :
    SmoothAtSubset S q.val := by
  classical
  obtain ⟨l,W,hWT,hW,hqW,D,hD,⟨f⟩⟩ := hq
  let Z : Set S := e.toHomeomorph ⁻¹' ((Subtype.val : T → Affine m) ⁻¹' W)
  let W' := (Subtype.val : S → Affine n) '' Z
  have hW'S : W' ⊆ S := by rintro x ⟨z,_,rfl⟩; exact z.property
  have hW' : IsOpen ((Subtype.val : S → Affine n) ⁻¹' W') := by
    have heq : (Subtype.val : S → Affine n) ⁻¹' W' = Z :=
      preimage_image_eq _ Subtype.val_injective
    rw [heq]
    exact hW.preimage e.toHomeomorph.continuous
  have he : ∀ x : S, x.val ∈ W' ↔ (e.toHomeomorph x).val ∈ W := by
    intro x
    change x.val ∈ (Subtype.val : S → Affine n) '' Z ↔ x ∈ Z
    constructor
    · rintro ⟨z,hz,hzx⟩
      exact (Subtype.val_injective hzx) ▸ hz
    · intro hx
      exact ⟨x,hx,rfl⟩
  exact ⟨l,W',hW'S,hW',⟨q,hqW,rfl⟩,D,hD,
    ⟨(e.restrict hW'S hWT he).trans f⟩⟩

theorem minimalPrime_separating_element {R : Type*} [CommRing R]
    (I : Ideal R) (hfin : I.minimalPrimes.Finite) (J : I.minimalPrimes) :
    ∃ P : R, P ∉ J.val ∧ ∀ K : I.minimalPrimes, K ≠ J → P ∈ K.val := by
  classical
  let : Fintype I.minimalPrimes := hfin.fintype
  have hnot : ∀ K : I.minimalPrimes, K ≠ J → ¬ K.val ≤ J.val := by
    intro K hK hle
    have hrev : J.val ≤ K.val := J.property.2 K.property.1 hle
    exact hK (Subtype.ext (le_antisymm hle hrev))
  have hex : ∀ K : I.minimalPrimes, ∃ t : R,
      t ∉ J.val ∧ (K ≠ J → t ∈ K.val) := by
    intro K
    by_cases hK : K = J
    · exact ⟨1,J.property.isPrime.one_notMem,fun h => False.elim (h hK)⟩
    · obtain ⟨t,htK,htJ⟩ := Set.not_subset.mp (hnot K hK)
      exact ⟨t,htJ,fun _ => htK⟩
  choose t htJ htK using hex
  let : J.val.IsPrime := J.property.isPrime
  let P := ∏ K : I.minimalPrimes, t K
  refine ⟨P,?_,?_⟩
  · intro hp
    obtain ⟨K,_,hK⟩ := Ideal.IsPrime.prod_mem_iff.mp hp
    exact htJ K hK
  · intro K hK
    exact Ideal.prod_mem K.val (Finset.mem_univ K) (htK K hK)

theorem prime_zeroLocus_generic_smooth {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    ∃ Q : MvPolynomial (Fin n) ℂ, Q ∉ J ∧
      ∀ q ∈ MvPolynomial.zeroLocus ℂ J, MvPolynomial.eval q Q ≠ 0 →
        SmoothAtSubset (MvPolynomial.zeroLocus ℂ J) q := by
  obtain ⟨d,_,G,hG,hGi⟩ := exists_integral_inj_algHom_of_quotient J Ideal.IsPrime.ne_top'
  choose P hP using fun j : Fin d => Ideal.Quotient.mkₐ_surjective ℂ J (G (MvPolynomial.X j))
  obtain ⟨D,r,hD,_,hs⟩ := normalization_analytic_sheets J G hG hGi P hP
  let Q := MvPolynomial.bind₁ P D
  have hcomp : (Ideal.Quotient.mkₐ ℂ J).comp (MvPolynomial.bind₁ P) = G := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa using hP j
  have hQ : Q ∉ J := by
    intro hQ
    have he : (Ideal.Quotient.mkₐ ℂ J) Q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hQ
    change ((Ideal.Quotient.mkₐ ℂ J).comp (MvPolynomial.bind₁ P)) D = 0 at he
    rw [hcomp] at he
    exact hD (hG (he.trans (map_zero G).symm))
  refine ⟨Q,hQ,fun q hq hqQ => ?_⟩
  let π : Affine n → Affine d := fun z j => MvPolynomial.eval z (P j)
  have hπ : AnalyticOnNhd ℂ π univ :=
    AnalyticOnNhd.pi (fun j => AnalyticOnNhd.eval_mvPolynomial (P j))
  have hqD : MvPolynomial.eval (π q) D ≠ 0 := by
    convert! hqQ using 1
    exact (MvPolynomial.aeval_bind₁ q P D).symm
  obtain ⟨I,g,A,_,hA,hqa,hg,hsheets⟩ := hs (π q) hqD
  obtain ⟨W,hWV,hW,hqW,B,hB,hWB⟩ :=
    finite_analytic_sheets_chart _ π hπ hA g hg hsheets hq hqa
  exact ⟨d,W,hWV,hW,hqW,B,hB,hWB⟩

theorem relative_open_trans {X : Type*} [TopologicalSpace X] {S T W : Set X}
    (_hTS : T ⊆ S) (hWT : W ⊆ T)
    (hT : IsOpen ((Subtype.val : S → X) ⁻¹' T))
    (hW : IsOpen ((Subtype.val : T → X) ⁻¹' W)) :
    IsOpen ((Subtype.val : S → X) ⁻¹' W) := by
  obtain ⟨O,hO,he⟩ := isOpen_induced_iff.mp hW
  have heq : (Subtype.val : S → X) ⁻¹' W =
      ((Subtype.val : S → X) ⁻¹' T) ∩ ((Subtype.val : S → X) ⁻¹' O) := by
    ext x
    constructor
    · intro hx
      refine ⟨hWT hx,?_⟩
      have hmem : (⟨x.val,hWT hx⟩ : T) ∈ (Subtype.val : T → X) ⁻¹' W := hx
      rw [← he] at hmem
      exact hmem
    · intro hx
      have hmem : (⟨x.val,hx.1⟩ : T) ∈ (Subtype.val : T → X) ⁻¹' O := hx.2
      rw [he] at hmem
      exact hmem
  rw [heq]
  exact hT.inter (hO.preimage continuous_subtype_val)

theorem smoothAtSubset_of_open_subset {n : ℕ} {S T : Set (Affine n)}
    (hTS : T ⊆ S) (hT : IsOpen ((Subtype.val : S → Affine n) ⁻¹' T))
    {q : Affine n} (hq : SmoothAtSubset T q) : SmoothAtSubset S q := by
  obtain ⟨m,W,hWT,hW,hqW,D,hD,e⟩ := hq
  exact ⟨m,W,hWT.trans hTS,relative_open_trans hTS hWT hT hW,hqW,D,hD,e⟩

theorem zeroLocus_polynomial_smooth_patch {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) {U : Set (Affine n)}
    (hUI : U ⊆ MvPolynomial.zeroLocus ℂ I)
    (hU : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U))
    (hne : U.Nonempty) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      (∃ q ∈ U, MvPolynomial.eval q P ≠ 0) ∧
      ∀ q ∈ MvPolynomial.zeroLocus ℂ I, MvPolynomial.eval q P ≠ 0 →
        SmoothAtSubset (MvPolynomial.zeroLocus ℂ I) q := by
  classical
  obtain ⟨a,ha⟩ := hne
  obtain ⟨J,haJ⟩ := mem_iUnion.mp ((zeroLocus_eq_union_minimalPrimes I).subset (hUI ha))
  let : J.val.IsPrime := J.property.isPrime
  obtain ⟨Q,hQ,hQK⟩ := minimalPrime_separating_element I
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I) J
  obtain ⟨R,hR,hRg⟩ := prime_zeroLocus_generic_smooth J.val
  let P := Q * R
  have hP : P ∉ J.val := fun hp =>
    (J.property.isPrime.mem_or_mem hp).elim hQ hR
  have hJU : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ J.val → Affine n) ⁻¹' U) :=
    hU.preimage (Topology.IsEmbedding.inclusion (MvPolynomial.zeroLocus_anti_mono J.property.le)).continuous
  obtain ⟨b,hbP,hbU⟩ := (prime_zeroLocus_dense_polynomial_nonzero J.val P hP).exists_mem_open
    hJU ⟨⟨a,haJ⟩,ha⟩
  refine ⟨P,⟨b.val,hbU,hbP⟩,fun q hq hqP => ?_⟩
  let V := MvPolynomial.zeroLocus ℂ I
  let T := MvPolynomial.zeroLocus ℂ J.val
  let O := {z : Affine n | MvPolynomial.eval z P ≠ 0}
  have hO : IsOpen O := (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).isOpen_compl
  have hTV : T ⊆ V := MvPolynomial.zeroLocus_anti_mono J.property.le
  have hVO : V ∩ O = T ∩ O := by
    apply subset_antisymm
    · intro z hz
      obtain ⟨K,hzK⟩ := mem_iUnion.mp ((zeroLocus_eq_union_minimalPrimes I).subset hz.1)
      have hK : K = J := by
        by_contra hK
        apply hz.2
        change MvPolynomial.eval z (Q * R) = 0
        have hzQ : MvPolynomial.eval z Q = 0 := hzK Q (hQK K hK)
        rw [map_mul, hzQ, zero_mul]
      exact ⟨by simpa only [hK] using hzK,hz.2⟩
    · exact fun z hz => ⟨hTV hz.1,hz.2⟩
  have hqT : q ∈ T := (hVO.subset ⟨hq,hqP⟩).1
  have hqR : MvPolynomial.eval q R ≠ 0 := by
    intro he
    apply hqP
    simp only [P, map_mul, he, mul_zero]
  have hTs : SmoothAtSubset T q := hRg q hqT hqR
  have hTo : IsOpen ((Subtype.val : T → Affine n) ⁻¹' (T ∩ O)) := by
    have he : (Subtype.val : T → Affine n) ⁻¹' (T ∩ O) = Subtype.val ⁻¹' O := by
      ext x; simp only [mem_preimage, mem_inter_iff, x.property, true_and]
    rw [he]
    exact
      hO.preimage (continuous_subtype_val : Continuous (Subtype.val : T → Affine n))
  have hUs := smoothAtSubset_restrict_open inter_subset_left hTo ⟨hqT,hqP⟩ hTs
  rw [← hVO] at hUs
  apply smoothAtSubset_of_open_subset inter_subset_left _ hUs
  have he : (Subtype.val : V → Affine n) ⁻¹' (V ∩ O) = Subtype.val ⁻¹' O := by
    ext x; simp only [mem_preimage, mem_inter_iff, x.property, true_and]
  rw [he]
  exact
    hO.preimage (continuous_subtype_val : Continuous (Subtype.val : V → Affine n))

 theorem IsAffineAlgebraic.polynomial_smooth_patch {n : ℕ}
    {V U : Set (Affine n)} (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U)) (hne : U.Nonempty) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      (∃ q ∈ U, MvPolynomial.eval q P ≠ 0) ∧
      ∀ q ∈ V, MvPolynomial.eval q P ≠ 0 → SmoothAtSubset V q := by
  let I := MvPolynomial.vanishingIdeal ℂ V
  have hIV : MvPolynomial.zeroLocus ℂ I = V := hV.zeroLocus_vanishingIdeal
  rw [← hIV] at hUV hU ⊢
  exact zeroLocus_polynomial_smooth_patch I hUV hU hne

end Release061

end OAI
