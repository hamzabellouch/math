import Mathlib
import OAI.Analysis.LaughlinGap.Contraction

namespace OAI

/-! Normal Order. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

noncomputable def bodySpace (n k : ℕ) : Submodule ℂ (Module.End ℂ (Hilbert n)) :=
  (exteriorLift (n := n) (k := k)).range

@[simp] lemma exteriorLift_single {n k : ℕ} (A B : BasisLabel n k) (c : ℂ) :
    exteriorLift (Matrix.single A B c) = c • ((basisContraction A).adjoint * basisContraction B) := by
  classical
  simp [exteriorLift, matrixLift, Matrix.single_apply, ite_smul, ite_and]

lemma word_rankOne_mem_bodySpace {n k : ℕ} (js ks : List (Fin n))
    (hj : js.length = k) (hk : ks.length = k) :
    (word js).adjoint * word ks ∈ bodySpace n k := by
  classical
  by_cases hn : js.Nodup
  · by_cases hm : ks.Nodup
    · obtain ⟨c,hc⟩ := word_normal_form js
      obtain ⟨d,hd⟩ := word_normal_form ks
      let A : BasisLabel n k := ⟨js.toFinset, (List.toFinset_card_of_nodup hn).trans hj⟩
      let B : BasisLabel n k := ⟨ks.toFinset, (List.toFinset_card_of_nodup hm).trans hk⟩
      have hA : word js = c • basisContraction A := hc
      have hB : word ks = d • basisContraction B := hd
      rw [hA,hB,map_smulₛₗ,smul_mul_assoc,mul_smul_comm,smul_smul]
      exact ⟨Matrix.single A B ((starRingEnd ℂ) c * d), exteriorLift_single _ _ _⟩
    · rw [word_eq_zero_of_not_nodup ks hm, mul_zero]
      exact (bodySpace n k).zero_mem
  · rw [word_eq_zero_of_not_nodup js hn, map_zero, zero_mul]
    exact (bodySpace n k).zero_mem

lemma triple_basic_eq_word {n : ℕ} (i : Fin n) (a : PairLabel n) :
    annihilation i * basicPair a = word [a.val.1,a.val.2,i] := by
  simp only [basicPair, word_cons, word_nil, one_mul, mul_assoc]

lemma triple_rankOne_mem_bodySpace {n : ℕ} (v w : PairLabel n → ℂ) (i j : Fin n) :
    (annihilation i * pairContraction v).adjoint *
      (annihilation j * pairContraction w) ∈ bodySpace n 3 := by
  classical
  simp only [pairContraction, Finset.mul_sum, mul_smul_comm, map_sum,
    map_smulₛₗ]
  simp only [Finset.sum_mul]
  simp only [smul_mul_assoc, Finset.smul_sum, smul_smul]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  apply Submodule.smul_mem
  rw [triple_basic_eq_word, triple_basic_eq_word]
  exact word_rankOne_mem_bodySpace _ _ rfl rfl

lemma middle_rankOne_mem_bodySpace {n : ℕ} (v w : PairLabel n → ℂ) (i j : Fin n) :
    (pairContraction v).adjoint * (creation i * annihilation j) * pairContraction w ∈
      bodySpace n 3 := by
  convert triple_rankOne_mem_bodySpace v w i j using 1
  rw [adjoint_mul, annihilation_adjoint]
  simp only [mul_assoc]

theorem pairThreeTerm_mem_bodySpace {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : pairThreeTerm v ∈ bodySpace n 3 := by
  classical
  unfold pairThreeTerm
  apply Submodule.sum_mem
  intro p _
  apply Submodule.sum_mem
  intro r _
  simp only [pairOneContraction, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  apply Submodule.smul_mem
  simp only [oneContraction, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul,
    mul_ite, ite_mul, mul_zero, zero_mul]
  have h (i j : Fin n) := middle_rankOne_mem_bodySpace (v p) (v r) i j
  have hc (P : Prop) [Decidable P] (i j : Fin n) :
      (if P then (pairContraction (v p)).adjoint * (creation i * annihilation j) *
        pairContraction (v r) else 0) ∈ bodySpace n 3 := by
    split_ifs
    · exact h i j
    · exact (bodySpace n 3).zero_mem
  exact Submodule.sub_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (hc _ _ _))
      (hc _ _ _)) (hc _ _ _)) (hc _ _ _)

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma homogeneous_smul {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) (c : ℂ) :
    Homogeneous k (c • x) := by
  intro A hA
  simp [hx A hA]

lemma homogeneous_sum {n k : ℕ} {ι : Type*} (s : Finset ι) (x : ι → Hilbert n)
    (hx : ∀ i ∈ s, Homogeneous k (x i)) : Homogeneous k (∑ i ∈ s, x i) := by
  intro A hA
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i hi => hx i hi A hA)

lemma vacuum_homogeneous (n : ℕ) : Homogeneous 0 (vacuum n) := by
  intro A hA
  have hh : A ≠ ∅ := by intro h; apply hA; simp [h]
  simp [vacuum_apply, hh]

lemma creation_homogeneous {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x)
    (i : Fin n) : Homogeneous (k+1) (creation i x) := by
  intro A hA
  by_cases hi : i ∈ A
  · have hc : (A.erase i).card ≠ k := by
      have hh := Finset.card_erase_add_one hi
      omega
    simp [transition_apply, hi, hx _ hc]
  · simp [transition_apply, hi]

lemma pairContraction_adjoint_homogeneous {n k : ℕ} (v : PairLabel n → ℂ)
    {x : Hilbert n} (hx : Homogeneous k x) :
    Homogeneous (k+2) ((pairContraction v).adjoint x) := by
  simp only [pairContraction, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply]
  apply homogeneous_sum
  intro a _
  apply homogeneous_smul
  simpa only [basicPair, adjoint_mul, annihilation_adjoint, Module.End.mul_apply] using
    creation_homogeneous (creation_homogeneous hx a.val.2) a.val.1

noncomputable def sectorReadout (n k : ℕ) : Hilbert n →ₗ[ℂ] ExteriorCoordinates n k where
  toFun x := WithLp.toLp 2 (fun A => x A.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma sectorReadout_apply {n k : ℕ} (x : Hilbert n) (A : BasisLabel n k) :
    sectorReadout n k x A = x A.val := rfl

lemma fullContraction_eq_exteriorContraction {n k : ℕ} {x : Hilbert n}
    (hx : Homogeneous k x) :
    fullContraction x = exteriorContraction (sectorReadout n k x) := by
  classical
  change (∑ A, star (x A) • allBasisContraction A) =
    ∑ A : BasisLabel n k, star (x A.val) • basisContraction A
  calc
    (∑ A, star (x A) • allBasisContraction A) =
        ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => A.card = k),
          star (x A) • allBasisContraction A := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro A _ hA
      have hh : A.card ≠ k := by simpa using hA
      simp [hx A hh]
    _ = _ := Finset.sum_subtype _ (by simp) _

lemma reconstruct_pair_product {n : ℕ} (v w : PairLabel n → ℂ) :
    reconstruct (pairContraction v * pairContraction w) = pairContraction v * pairContraction w := by
  simp only [pairContraction, Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  have he : basicPair a * basicPair b = word [b.val.1,b.val.2,a.val.1,a.val.2] := by
    simp only [basicPair, word_cons, word_nil, one_mul, mul_assoc]
  rw [he,reconstruct_word]

noncomputable def pairWedgeColumn {n : ℕ} (v w : PairLabel n → ℂ) : ExteriorCoordinates n 4 :=
  sectorReadout n 4 ((pairContraction w * pairContraction v).adjoint (vacuum n))

lemma pairWedgeColumn_contraction {n : ℕ} (v w : PairLabel n → ℂ) :
    exteriorContraction (pairWedgeColumn v w) = pairContraction w * pairContraction v := by
  have hh : Homogeneous 4 ((pairContraction w * pairContraction v).adjoint (vacuum n)) := by
    rw [adjoint_mul, Module.End.mul_apply]
    exact pairContraction_adjoint_homogeneous v
      (pairContraction_adjoint_homogeneous w (vacuum_homogeneous n))
  rw [pairWedgeColumn, ← fullContraction_eq_exteriorContraction hh]
  exact reconstruct_pair_product w v

noncomputable def pairWedgeMatrix {n : ℕ} {ι : Type*} (v : ι → PairLabel n → ℂ) :
    Matrix (BasisLabel n 4) (ι × ι) ℂ := fun A pr => pairWedgeColumn (v pr.1) (v pr.2) A

theorem pairFourTerm_eq_lift {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) :
    pairFourTerm v = exteriorLift (pairWedgeMatrix v * (pairWedgeMatrix v).conjTranspose) := by
  classical
  have hw := matrixLift_columns basisContraction (pairWedgeMatrix v) (1 : Matrix (ι × ι) (ι × ι) ℂ)
  simp only [Matrix.mul_one] at hw
  rw [exteriorLift, hw]
  have he (pr : ι × ι) :
      contractCombination basisContraction (fun A => pairWedgeMatrix v A pr) =
        pairContraction (v pr.2) * pairContraction (v pr.1) :=
    pairWedgeColumn_contraction (v pr.1) (v pr.2)
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, he,
    Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fintype.sum_prod_type]
  rfl

theorem pairFourTerm_positive {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : (pairFourTerm v).IsPositive := by
  rw [pairFourTerm_eq_lift]
  exact exteriorLift_positive (Matrix.posSemidef_self_mul_conjTranspose _)

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma pairContraction_eq_pairAnnihilator {n : ℕ} (v : Fin n → Fin n → ℂ) :
    pairContraction (fun a => v a.val.1 a.val.2) = pairAnnihilator v := by
  classical
  simp only [pairContraction, basicPair]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
    (by simp) (fun a => star (v a.1 a.2) • (annihilation a.2 * annihilation a.1))]
  simp only [Finset.sum_filter, Fintype.sum_prod_type, pairAnnihilator]

lemma sectorInclusion_readout {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) :
    sectorInclusion n k (sectorReadout n k x) = x := by
  ext A
  by_cases hA : A.card = k
  · simp [sectorInclusion_apply, hA]
  · simp [sectorInclusion_apply, hA, hx A hA]

lemma sectorInclusion_adjoint (n k : ℕ) : (sectorInclusion n k).adjoint = sectorReadout n k := by
  classical
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  let f : Finset (Fin n) → ℂ := fun A => inner ℂ (x A) (sectorInclusion n k y A)
  calc
    (∑ A : BasisLabel n k, inner ℂ (sectorReadout n k x A) (y A)) =
        ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => A.card = k), f A := by
      have h := Finset.sum_subtype (p := fun A : Finset (Fin n) => A.card = k) (F := inferInstance) (Finset.univ.filter (fun A : Finset (Fin n) => A.card = k))
        (by simp) f
      simpa only [f, sectorInclusion_apply_label, sectorReadout_apply] using h.symm
    _ = ∑ A, inner ℂ (x A) (sectorInclusion n k y A) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro A _ hA
      have hh : A.card ≠ k := by simpa using hA
      simp [f, sectorInclusion_apply, hh]

noncomputable def sectorExtract (n k : ℕ) :
    Module.End ℂ (Hilbert n) →ₗ[ℂ] Matrix (BasisLabel n k) (BasisLabel n k) ℂ where
  toFun T := Matrix.toEuclideanLin.symm (sectorReadout n k ∘ₗ T ∘ₗ sectorInclusion n k)
  map_add' _ _ := by simp only [LinearMap.comp_add, LinearMap.add_comp, map_add]
  map_smul' _ _ := by simp only [LinearMap.comp_smul, LinearMap.smul_comp, map_smul, RingHom.id_apply]

@[simp] lemma sectorExtract_toEuclideanLin (n k : ℕ) (T : Module.End ℂ (Hilbert n)) :
    (sectorExtract n k T).toEuclideanLin = sectorReadout n k ∘ₗ T ∘ₗ sectorInclusion n k :=
  Matrix.toEuclideanLin.apply_symm_apply _

@[simp] theorem sectorExtract_exteriorLift {n k : ℕ}
    (M : Matrix (BasisLabel n k) (BasisLabel n k) ℂ) :
    sectorExtract n k (exteriorLift M) = M := by
  apply Matrix.toEuclideanLin.injective
  rw [sectorExtract_toEuclideanLin]
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (sectorReadout n k (exteriorLift M (sectorInclusion n k y))) = _
  rw [← sectorInclusion_adjoint, LinearMap.adjoint_inner_right]
  exact exteriorLift_inner_sector M x y

lemma exteriorLift_sectorExtract {n k : ℕ} {T : Module.End ℂ (Hilbert n)}
    (hT : T ∈ bodySpace n k) : exteriorLift (sectorExtract n k T) = T := by
  obtain ⟨M,rfl⟩ := hT
  rw [sectorExtract_exteriorLift]

lemma sectorExtract_mul {n k : ℕ} (T S : Module.End ℂ (Hilbert n))
    (hS : ∀ x, Homogeneous k x → Homogeneous k (S x)) :
    sectorExtract n k (T * S) = sectorExtract n k T * sectorExtract n k S := by
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, sectorExtract_toEuclideanLin]
  apply LinearMap.ext
  intro x
  change sectorReadout n k (T (S (sectorInclusion n k x))) =
    sectorReadout n k (T (sectorInclusion n k (sectorReadout n k (S (sectorInclusion n k x)))))
  rw [sectorInclusion_readout (hS _ (sectorInclusion_homogeneous x))]

lemma sectorExtract_eq_zero {n k : ℕ} (T : Module.End ℂ (Hilbert n))
    (hT : ∀ x, Homogeneous k x → T x = 0) : sectorExtract n k T = 0 := by
  apply Matrix.toEuclideanLin.injective
  rw [map_zero, sectorExtract_toEuclideanLin]
  apply LinearMap.ext
  intro x
  change sectorReadout n k (T (sectorInclusion n k x)) = 0
  rw [hT _ (sectorInclusion_homogeneous x), map_zero]

lemma pairContraction_homogeneous {n k : ℕ} (v : PairLabel n → ℂ)
    {x : Hilbert n} (hx : Homogeneous (k+2) x) : Homogeneous k (pairContraction v x) := by
  simp only [pairContraction, LinearMap.sum_apply, LinearMap.smul_apply]
  apply homogeneous_sum
  intro a _
  apply homogeneous_smul
  exact annihilation_homogeneous (annihilation_homogeneous hx a.val.1) a.val.2

lemma pairHamiltonian_homogeneous {n k : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) {x : Hilbert n} (hx : Homogeneous (k+2) x) :
    Homogeneous (k+2) (pairHamiltonian v x) := by
  simp only [pairHamiltonian, LinearMap.sum_apply, Module.End.mul_apply]
  exact homogeneous_sum _ _ (fun p _ => pairContraction_adjoint_homogeneous _
    (pairContraction_homogeneous _ hx))

lemma numberOperator_apply {n : ℕ} (x : Hilbert n) (A : Finset (Fin n)) :
    (∑ i : Fin n, creation i (annihilation i x)) A = (A.card : ℂ) * x A := by
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  have ht (i : Fin n) : creation i (annihilation i x) A = if i ∈ A then x A else 0 := by
    by_cases hi : i ∈ A <;>
      simp [transition_apply, hi, ← mul_assoc]
  simp only [ht]
  rw [← Finset.sum_filter]
  simp

lemma numberOperator_one {n : ℕ} {x : Hilbert n} (hx : Homogeneous 1 x) :
    (∑ i : Fin n, creation i (annihilation i x)) = x := by
  ext A
  rw [numberOperator_apply]
  by_cases hA : A.card = 1
  · simp [hA]
  · simp [hx A hA]

noncomputable def pairTripleOperator {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) : Module.End ℂ (Hilbert n) :=
  ∑ p, ∑ i : Fin n, (annihilation i * pairContraction (v p)).adjoint *
    (annihilation i * pairContraction (v p))

lemma pairTripleOperator_three {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) {x : Hilbert n} (hx : Homogeneous 3 x) :
    pairTripleOperator v x = pairHamiltonian v x := by
  simp only [pairTripleOperator, pairHamiltonian, LinearMap.sum_apply,
    adjoint_mul, annihilation_adjoint, Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [← map_sum, numberOperator_one (pairContraction_homogeneous (v p) hx)]

lemma reconstruct_triple_pair {n : ℕ} (v : PairLabel n → ℂ) (i : Fin n) :
    reconstruct (annihilation i * pairContraction v) = annihilation i * pairContraction v := by
  simp only [pairContraction, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    triple_basic_eq_word, reconstruct_word]

noncomputable def tripleWedgeColumn {n : ℕ} (v : PairLabel n → ℂ) (i : Fin n) :
    ExteriorCoordinates n 3 :=
  sectorReadout n 3 ((annihilation i * pairContraction v).adjoint (vacuum n))

lemma tripleWedgeColumn_contraction {n : ℕ} (v : PairLabel n → ℂ) (i : Fin n) :
    exteriorContraction (tripleWedgeColumn v i) = annihilation i * pairContraction v := by
  have hh : Homogeneous 3 ((annihilation i * pairContraction v).adjoint (vacuum n)) := by
    rw [adjoint_mul, annihilation_adjoint, Module.End.mul_apply]
    exact pairContraction_adjoint_homogeneous v (creation_homogeneous (vacuum_homogeneous n) i)
  rw [tripleWedgeColumn, ← fullContraction_eq_exteriorContraction hh]
  exact reconstruct_triple_pair v i

noncomputable def tripleWedgeMatrix {n : ℕ} {ι : Type*} (v : ι → PairLabel n → ℂ) :
    Matrix (BasisLabel n 3) (ι × Fin n) ℂ := fun A pi => tripleWedgeColumn (v pi.1) pi.2 A

lemma pairTripleOperator_eq_lift {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) :
    pairTripleOperator v = exteriorLift (tripleWedgeMatrix v * (tripleWedgeMatrix v).conjTranspose) := by
  classical
  have hw := matrixLift_columns basisContraction (tripleWedgeMatrix v)
    (1 : Matrix (ι × Fin n) (ι × Fin n) ℂ)
  simp only [Matrix.mul_one] at hw
  rw [exteriorLift, hw]
  have he (pi : ι × Fin n) :
      contractCombination basisContraction (fun A => tripleWedgeMatrix v A pi) =
        annihilation pi.2 * pairContraction (v pi.1) := tripleWedgeColumn_contraction _ _
  simp only [matrixLift, LinearMap.coe_mk, AddHom.coe_mk, he,
    Matrix.one_apply, ite_smul, one_smul, zero_smul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Fintype.sum_prod_type]
  rfl

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma pairHamiltonian_sector_three {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) :
    sectorExtract n 3 (pairHamiltonian v) = tripleWedgeMatrix v * (tripleWedgeMatrix v).conjTranspose := by
  rw [← sectorExtract_exteriorLift (tripleWedgeMatrix v * (tripleWedgeMatrix v).conjTranspose),
    ← pairTripleOperator_eq_lift]
  apply Matrix.toEuclideanLin.injective
  rw [sectorExtract_toEuclideanLin, sectorExtract_toEuclideanLin]
  apply LinearMap.ext
  intro x
  change sectorReadout n 3 (pairHamiltonian v (sectorInclusion n 3 x)) =
    sectorReadout n 3 (pairTripleOperator v (sectorInclusion n 3 x))
  rw [pairTripleOperator_three v (sectorInclusion_homogeneous x)]

theorem pairThreeTerm_eq_lift {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → PairLabel n → ℂ)
    (hv : ∀ p r, (∑ a, star (v p a) * v r a) = if p = r then 1 else 0) :
    pairThreeTerm v = exteriorLift (tripleWedgeMatrix v *
      ((tripleWedgeMatrix v).conjTranspose * tripleWedgeMatrix v - 1) *
      (tripleWedgeMatrix v).conjTranspose) := by
  have h4 : sectorExtract n 3 (pairFourTerm v) = 0 := by
    apply sectorExtract_eq_zero
    intro x hx
    rw [pairFourTerm_eq_lift]
    exact exteriorLift_eq_zero_of_degree_lt hx (by omega) _
  have he := congrArg (sectorExtract n 3) (pairHamiltonian_square v hv)
  rw [sectorExtract_mul _ _ (fun x hx => pairHamiltonian_homogeneous v hx),
    pairHamiltonian_sector_three v, map_add, map_add, pairHamiltonian_sector_three v,
    h4, add_zero] at he
  have h3 : sectorExtract n 3 (pairThreeTerm v) =
      tripleWedgeMatrix v * ((tripleWedgeMatrix v).conjTranspose * tripleWedgeMatrix v - 1) *
        (tripleWedgeMatrix v).conjTranspose := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc] at he ⊢
    exact eq_sub_of_add_eq' he.symm
  rw [← exteriorLift_sectorExtract (pairThreeTerm_mem_bodySpace v), h3]

theorem normal_ordered_square {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → PairLabel n → ℂ)
    (hv : ∀ p r, (∑ a, star (v p a) * v r a) = if p = r then 1 else 0) :
    pairHamiltonian v * pairHamiltonian v = pairHamiltonian v +
      exteriorLift (tripleWedgeMatrix v *
        ((tripleWedgeMatrix v).conjTranspose * tripleWedgeMatrix v - 1) *
        (tripleWedgeMatrix v).conjTranspose) +
      exteriorLift (pairWedgeMatrix v * (pairWedgeMatrix v).conjTranspose) := by
  rw [pairHamiltonian_square v hv, pairThreeTerm_eq_lift v hv, pairFourTerm_eq_lift]

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma sum_increasing_pairs {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    2 * (∑ a : PairLabel n, f a.val.1 a.val.2) = ∑ i, ∑ j, f i j := by
  classical
  have htri : (∑ a : PairLabel n, f a.val.1 a.val.2) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
      (by simp) (fun a => f a.1 a.2)]
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have he (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h, hs i j]
  rw [htri]
  conv_rhs => arg 2; intro i; arg 2; intro j; rw [he i j]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin n => if j < i then f j i else 0)]
  ring

lemma sphericalExteriorPairCoefficient_eq_tensor (Q p : ℕ) (i j : Fin (Q+1)) :
    sphericalExteriorPairCoefficient Q p i.val j.val = Real.sqrt 2 * pairCoefficient Q p i j := by
  unfold sphericalExteriorPairCoefficient pairCoefficient
  split_ifs
  · have h : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
  · simp

noncomputable def physicalPairForms (Q : ℕ) : Fin (2*Q-1) → PairLabel (Q+1) → ℂ := fun p a =>
  (sphericalExteriorPairCoefficient Q p.val a.val.1.val a.val.2.val : ℂ)

lemma physicalPair_contraction (Q : ℕ) (p : Fin (2*Q-1)) :
    pairContraction (physicalPairForms Q p) = localPair (Q+1) Q p.val := by
  exact pairContraction_eq_pairAnnihilator (fun x y : Fin (Q+1) =>
    (sphericalExteriorPairCoefficient Q p.val x.val y.val : ℂ))

theorem physicalPairForms_orthonormal {Q : ℕ} (hQ : 2 ≤ Q) :
    ∀ p r, (∑ a, star (physicalPairForms Q p a) * physicalPairForms Q r a) =
      if p = r then 1 else 0 := by
  intro p r
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hprod (a : PairLabel (Q+1)) :
      star (physicalPairForms Q p a) * physicalPairForms Q r a =
      ((2 * (pairCoefficient Q p.val a.val.1 a.val.2 *
        pairCoefficient Q r.val a.val.1 a.val.2) : ℝ) : ℂ) := by
    simp only [physicalPairForms, sphericalExteriorPairCoefficient_eq_tensor,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    linear_combination (pairCoefficient Q p.val a.val.1 a.val.2 *
      pairCoefficient Q r.val a.val.1 a.val.2) * hs
  simp_rw [hprod]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum]
  have hsum := sum_increasing_pairs
    (fun i j : Fin (Q+1) => pairCoefficient Q p.val i j * pairCoefficient Q r.val i j)
    (by intro i j; rw [pairCoefficient_swap Q p.val j i, pairCoefficient_swap Q r.val j i]; ring)
    (by intro i; simp [pairCoefficient])
  rw [hsum, ← pairVector_inner]
  exact (orthonormal_iff_ite.mp (pairVector_orthonormal Q hQ)) p r

noncomputable def physicalOccupationHamiltonian (Q : ℕ) : Module.End ℂ (Hilbert (Q+1)) :=
  pairHamiltonian (physicalPairForms Q)

theorem physical_normal_ordered_square {Q : ℕ} (hQ : 2 ≤ Q) :
    physicalOccupationHamiltonian Q * physicalOccupationHamiltonian Q =
      physicalOccupationHamiltonian Q +
      exteriorLift (tripleWedgeMatrix (physicalPairForms Q) *
        ((tripleWedgeMatrix (physicalPairForms Q)).conjTranspose *
          tripleWedgeMatrix (physicalPairForms Q) - 1) *
        (tripleWedgeMatrix (physicalPairForms Q)).conjTranspose) +
      exteriorLift (pairWedgeMatrix (physicalPairForms Q) *
        (pairWedgeMatrix (physicalPairForms Q)).conjTranspose) :=
  normal_ordered_square _ (physicalPairForms_orthonormal hQ)

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct ComplexOrder

lemma pairContraction_eq_zero_of_degree_lt {n k : ℕ} (v : PairLabel n → ℂ)
    {x : Hilbert n} (hx : Homogeneous k x) (hk : k < 2) : pairContraction v x = 0 := by
  simp only [pairContraction, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro a _
  have he : basicPair a = word [a.val.1,a.val.2] := by
    simp only [basicPair, word_cons, word_nil, one_mul]
  rw [he, word_eq_zero_of_degree_lt _ hx (by simpa using hk), smul_zero]

lemma pairHamiltonian_preserves_degree {n k : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → PairLabel n → ℂ) {x : Hilbert n} (hx : Homogeneous k x) :
    Homogeneous k (pairHamiltonian v x) := by
  by_cases hk : 2 ≤ k
  · obtain ⟨l, rfl⟩ : ∃ l, k = l+2 := ⟨k-2, by omega⟩
    exact pairHamiltonian_homogeneous v hx
  · have he : pairHamiltonian v x = 0 := by
      simp only [pairHamiltonian, LinearMap.sum_apply, Module.End.mul_apply,
        pairContraction_eq_zero_of_degree_lt _ hx (by omega), map_zero, Finset.sum_const_zero]
    rw [he]
    exact fun _ _ => rfl

theorem physicalOccupationHamiltonian_positive (Q : ℕ) :
    (physicalOccupationHamiltonian Q).IsPositive := by
  apply LinearMap.isPositive_sum
  intro p _
  exact LinearMap.isPositive_adjoint_comp_self _

theorem physicalOccupationHamiltonian_inner (Q : ℕ) (x : Hilbert (Q+1)) :
    (inner ℂ x (physicalOccupationHamiltonian Q x)).re =
      localPairEnergy (Q+1) (2*Q-1) Q x := by
  simp only [physicalOccupationHamiltonian, pairHamiltonian, LinearMap.sum_apply,
    inner_sum, Complex.re_sum, localPairEnergy]
  apply Finset.sum_congr rfl
  intro p _
  change (inner ℂ x ((pairContraction (physicalPairForms Q p)).adjoint
    (pairContraction (physicalPairForms Q p) x))).re = _
  rw [LinearMap.adjoint_inner_right, physicalPair_contraction]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

end LaughlinGap.Occupation

namespace LaughlinGap.Occupation
open scoped BigOperators InnerProduct

lemma numberOperator_homogeneous {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) :
    (∑ i : Fin n, creation i (annihilation i x)) = (k : ℂ) • x := by
  ext A
  rw [numberOperator_apply]
  change (A.card : ℂ) * x A = (k : ℂ) * x A
  by_cases hA : A.card = k
  · rw [hA]
  · rw [hx A hA, mul_zero, mul_zero]

lemma sum_annihilation_norm_sq {n k : ℕ} {x : Hilbert n} (hx : Homogeneous k x) :
    ∑ i : Fin n, ‖annihilation i x‖ ^ 2 = (k : ℝ) * ‖x‖ ^ 2 := by
  have h := congrArg (fun y : Hilbert n => (inner ℂ x y).re) (numberOperator_homogeneous hx)
  simp only [inner_sum, Complex.re_sum, ← annihilation_adjoint,
    LinearMap.adjoint_inner_right, inner_smul_right,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at h
  have hr (y : Hilbert n) : (inner ℂ y y).re = ‖y‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) y).symm
  simpa only [hr] using h

noncomputable def rawReadout (n N : ℕ) : Hilbert n →ₗ[ℂ] EuclideanSpace ℂ (Fin N → Fin n) where
  toFun x := WithLp.toLp 2 (fun a => word (List.ofFn a) x ∅)
  map_add' x y := by ext a; simp only [map_add, PiLp.add_apply]
  map_smul' c x := by ext a; simp only [map_smul, RingHom.id_apply, PiLp.smul_apply]

@[simp] lemma rawReadout_apply {n N : ℕ} (x : Hilbert n) (a : Fin N → Fin n) :
    rawReadout n N x a = word (List.ofFn a) x ∅ := rfl

lemma rawReadout_succ {n N : ℕ} (x : Hilbert n) (a : Fin (N+1) → Fin n) :
    rawReadout n (N+1) x a = rawReadout n N (annihilation (a 0) x) (fun i => a i.succ) := by
  simp only [rawReadout_apply, List.ofFn_succ, word_cons, Module.End.mul_apply]

theorem rawReadout_norm_sq {n N : ℕ} {x : Hilbert n} (hx : Homogeneous N x) :
    ‖rawReadout n N x‖ ^ 2 = (N.factorial : ℝ) * ‖x‖ ^ 2 := by
  induction N generalizing x with
  | zero =>
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_unique, rawReadout_apply, List.ofFn_zero, word_nil,
      Module.End.one_apply, Nat.factorial_zero, Nat.cast_one, one_mul]
    rw [degree_zero_eq_vacuum hx, norm_smul, vacuum_norm, mul_one]
    simp
  | succ N ih =>
    rw [EuclideanSpace.norm_sq_eq]
    rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Fin n)).sum_comp]
    simp only [Fintype.sum_prod_type]
    change (∑ i : Fin n, ∑ a : Fin N → Fin n,
      ‖rawReadout n (N+1) x (Fin.cons i a)‖ ^ 2) = _
    simp only [rawReadout_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [← EuclideanSpace.norm_sq_eq, ih (annihilation_homogeneous hx _)]
    rw [← Finset.mul_sum, sum_annihilation_norm_sq hx, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring

noncomputable def normalizedReadout (n N : ℕ) :
    Hilbert n →ₗ[ℂ] EuclideanSpace ℂ (Fin N → Fin n) :=
  ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) • rawReadout n N

@[simp] lemma normalizedReadout_apply {n N : ℕ} (x : Hilbert n) (a : Fin N → Fin n) :
    normalizedReadout n N x a =
      ((Real.sqrt (N.factorial : ℝ))⁻¹ : ℂ) * word (List.ofFn a) x ∅ := rfl

lemma normalizedReadout_norm_sq {n N : ℕ} {x : Hilbert n} (hx : Homogeneous N x) :
    ‖normalizedReadout n N x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hf : 0 < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hs : 0 < Real.sqrt (N.factorial : ℝ) := Real.sqrt_pos.mpr hf
  simp only [normalizedReadout, LinearMap.smul_apply, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow,
    inv_pow, Real.sq_sqrt hf.le, rawReadout_norm_sq hx]
  field_simp

end LaughlinGap.Occupation

end

end OAI
