import OAI.NumberTheory.DirichletL.Descent.HybridBound

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def slotTupleProduct (p : ι → Ideal Eis) : Ideal Eis := ∏ i, p i

theorem slotTupleProduct_injective_on
    (L : ι → Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P) :
    Set.InjOn (slotTupleProduct (ι := ι)) {p | ∀ i, p i ∈ L i} := by
  intro p hpL q hqL he
  funext i
  change (∏ i, p i) = ∏ i, q i at he
  have hdiv : p i ∣ ∏ j, q j := by
    rw [← he]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  obtain ⟨j, hj, hd⟩ := ((hp i (p i) (hpL i)).dvd_finsetProd_iff q).mp hdiv
  have hpq : p i = q j := associated_iff_eq.mp
    ((hp i (p i) (hpL i)).associated_of_dvd (hp j (q j) (hqL j)) hd)
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hL hne) (hpL i) (hpq.symm ▸ hqL j)
  simpa only [← hij] using hpq

omit [DecidableEq ι] in
theorem slotTupleProduct_admissible
    (L : ι → Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P)
    (hgen : ∀ i, ∀ P ∈ L i, primaryGenerator P ≠ 0)
    (p : ι → Ideal Eis) (hpL : ∀ i, p i ∈ L i) :
    CubicSieve.Admissible (slotTupleProduct p) := by
  constructor
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      have hpi := hp i (p i) (hpL i)
      have hpj := hp j (p j) (hpL j)
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime hpi).isMaximal hpi.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime hpj).isMaximal hpj.ne_zero
      apply (Ideal.isCoprime_of_isMaximal ?_).isRelPrime
      intro he
      exact Finset.disjoint_left.mp (hL hij) (hpL i) (he.symm ▸ hpL j)
    · intro i hi
      exact (hp i (p i) (hpL i)).squarefree
  · change primaryGeneratorHom (∏ i, p i) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hgen i (p i) (hpL i))

def slotProductCoefficient (tuples : Finset (ι → Ideal Eis))
    (a : (ι → Ideal Eis) → ℂ) (P : Ideal Eis) : ℂ :=
  ∑ p ∈ tuples, if slotTupleProduct p = P then a p else 0

omit [DecidableEq ι] in
theorem slotProductCoefficient_at_product
    (tuples : Finset (ι → Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)))
    (a : (ι → Ideal Eis) → ℂ) (p : ι → Ideal Eis) (hp : p ∈ tuples) :
    slotProductCoefficient tuples a (slotTupleProduct p) = a p := by
  unfold slotProductCoefficient
  rw [Finset.sum_eq_single p]
  · simp
  · intro q hq hqp
    exact ite_eq_right (fun he => hqp (hinj hq hp he))
  · exact fun hn => (hn hp).elim

omit [DecidableEq ι] in
theorem active_slot_hybrid_reindex
    (tuples : Finset (ι → Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)))
    (nset bset : Finset (Ideal Eis)) (a : (ι → Ideal Eis) → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    (∑ p ∈ tuples, a p / (Real.sqrt (Ideal.absNorm (slotTupleProduct p) : ℝ) : ℂ) *
      (if IsCoprime k (slotTupleProduct p) then 1 else 0) *
        hybridInner nset bset beta k (slotTupleProduct p)) =
      hybridRow (tuples.image slotTupleProduct) nset bset (slotProductCoefficient tuples a) beta k := by
  rw [hybridRow, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro p hp
  rw [slotProductCoefficient_at_product tuples hinj a p hp]

theorem active_slot_hybrid_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B V : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (L : ι → Finset (Ideal Eis)),
      Pairwise (fun i j => Disjoint (L i) (L j)) →
      (∀ i, ∀ P ∈ L i, Prime P) → (∀ i, ∀ P ∈ L i, primaryGenerator P ≠ 0) →
    ∀ (tuples : Finset (ι → Ideal Eis)), (∀ p ∈ tuples, ∀ i, p i ∈ L i) →
      (∀ p ∈ tuples, V ≤ (Ideal.absNorm (slotTupleProduct p) : ℝ) ∧
        (Ideal.absNorm (slotTupleProduct p) : ℝ) ≤ 2 * V) →
    ∀ (rows nset bset : Finset (Ideal Eis)) (a : (ι → Ideal Eis) → ℂ)
      (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ p ∈ tuples, ‖a p‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖∑ p ∈ tuples,
        a p / (Real.sqrt (Ideal.absNorm (slotTupleProduct p) : ℝ) : ℂ) *
        (if IsCoprime k (slotTupleProduct p) then 1 else 0) *
          hybridInner nset bset beta k (slotTupleProduct p)‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * V) := by
  obtain ⟨C, hC, he⟩ := hybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B V hK hN hB L hL hp hgen tuples htuples hnorm rows nset bset a beta
    hrows hn hb ha hbeta
  have hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)) :=
    (slotTupleProduct_injective_on L hL hp).mono htuples
  have hP : ∀ P ∈ tuples.image slotTupleProduct,
      CubicSieve.Admissible P ∧ V ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * V := by
    intro P hP
    obtain ⟨p, hpT, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨slotTupleProduct_admissible L hL hp hgen p (htuples p hpT), hnorm p hpT⟩
  have hcoeff : ∀ P ∈ tuples.image slotTupleProduct, ‖slotProductCoefficient tuples a P‖ ≤ 1 := by
    intro P hP
    obtain ⟨p, hpT, rfl⟩ := Finset.mem_image.mp hP
    rw [slotProductCoefficient_at_product tuples hinj a p hpT]
    exact ha p hpT
  simp_rw [active_slot_hybrid_reindex tuples hinj nset bset a beta]
  exact he K N B V hK hN hB rows nset bset (tuples.image slotTupleProduct)
    (slotProductCoefficient tuples a) beta hrows hn hb hP hcoeff hbeta

end
end SevenEighths.InverseMoment

end OAI
