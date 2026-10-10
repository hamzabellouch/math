import OAI.NumberTheory.DirichletL.Inversion.InitialMarkedDictionary

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialPhysicalSlots
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialMarkedDictionary
open InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def livePrimes (V : ℝ→ℂ) (b D : ℝ) : Finset (Ideal O) :=
  ((HeckePrimeAnnular.annulusSet b D).filter
    (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H)).filter
      (fun P=>V ((P.absNorm:ℝ)/D)≠0)

omit [NeZero M] in
theorem livePrime_data (V : ℝ→ℂ) (a b D : ℝ) (hD : 0<D)
    (hV : ∀x,V x≠0 → x∈Set.Icc a b) (P : Ideal O) (hp : P∈livePrimes M H V b D) :
    Prime P ∧ P∈RayQuotient.identityClass M H ∧ a*D≤(P.absNorm:ℝ) ∧ (P.absNorm:ℝ)≤b*D := by
  obtain ⟨hp,hv⟩ := Finset.mem_filter.mp hp
  obtain ⟨_,hp,hr⟩ := Finset.mem_filter.mp hp
  exact ⟨hp,hr,(le_div_iff₀ hD).mp (hV _ hv).1,(div_le_iff₀ hD).mp (hV _ hv).2⟩

omit [NeZero M] in
theorem amplitude_eq_live (u : O) (V : ℝ→ℂ) (b Z ell : ℝ) (ζ : ℂ) (hZ : 0<Z) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u V b (Z^ell) ζ=
      ((Z^(-ell/2):ℝ):ℂ)*∑P∈livePrimes M H V b (Z^ell),
        primeProfile V (Z^ell) ζ P*star (CanonicalRowCompletion.idealRowHom u P) := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude
  rw [normalization_eq Z ell hZ]
  congr 1
  rw [livePrimes]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  split_ifs with hv
  · change star (CanonicalRowCompletion.idealRowHom u P)*V _*_ =
      (V _*_)*star (CanonicalRowCompletion.idealRowHom u P)
    ring
  · simp only [not_not] at hv
    simp [hv]

theorem slot_normalization {ι : Type*} [Fintype ι] (Z : ℝ) (hZ : 0<Z) (ell : ι→ℝ) :
    (∏i,((Z^(-ell i/2):ℝ):ℂ))=((Z^(-(∑i,ell i)/2):ℝ):ℂ) := by
  rw [←Complex.ofReal_prod,←Real.rpow_sum_of_pos hZ]
  congr 2
  simp only [neg_div,Finset.sum_div,Finset.sum_neg_distrib]

omit [NeZero M] in
theorem amplitude_product_eq_tuples {ι : Type*} [Fintype ι] (u : O)
    (V : ι→ℝ→ℂ) (b ell : ι→ℝ) (ζ : ι→ℂ) (Z : ℝ) (hZ : 0<Z) :
    (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (Z^(ell i)) (ζ i))=
      ((Z^(-(∑i,ell i)/2):ℝ):ℂ)*
        ∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
        (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))*
          star (CanonicalRowCompletion.idealRowHom u (∏i,p i)) := by
  simp_rw [amplitude_eq_live M H _ _ _ _ _ _ hZ]
  rw [Finset.prod_mul_distrib,slot_normalization Z hZ,conjugate_mark_product]

omit [NeZero M] in
theorem physical_slots_norm_initial {ι : Type*} [Fintype ι]
    (data : RowData) (u : NonzeroElement) (W : ℝ→ℂ) (V : ι→ℝ→ℂ)
    (Z r σ freq bW : ℝ) (a b ell : ι→ℝ) (ζ : ι→ℂ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤bW) (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i)) :
    ‖polynomial (data.character u) true W (Z^r) σ freq*
      (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (Z^(ell i)) (ζ i))‖=
    ‖∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
      (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
        fixedBase data.η data.m data.f (∏i,p i))*
      originalTotalPolynomial
        ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
        (∏i,p i) (fixedBase data.η data.m data.f) (fun _=>1)
        (twistedProfile W σ freq) Z r (∑i,ell i) u.val‖ := by
  let T := fun i=>livePrimes M H (V i) (b i) (Z^(ell i))
  let A := fun p:ι→Ideal O=>∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i)
  have hn (p : ι→Ideal O) (hp : p∈Fintype.piFinset T) (_ha : A p≠0) :
      fixedBase data.η data.m data.f (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hpi := Fintype.mem_piFinset.mp hp i
    have hd := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
      (Real.rpow_pos_of_pos hZ _) (hV i) (p i) hpi
    exact base_nonzero_prime data (p i) hd.1 ((hlarge i).trans_le hd.2.2.1)
  have he := indexed_conjugate_mark_norm (Fintype.piFinset T) (fun p=>∏i,p i) A
    (fixedBase data.η data.m data.f) (data.character u) u.val
    (fixedBase_row data.η (data.character u) data.m data.f u.val (data.character_spec u))
    W Z r (∑i,ell i) σ freq hZ (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊)
    (finite_source_cover W (Z^r) bW (Real.rpow_pos_of_pos hZ _) hW) hn
  rw [amplitude_product_eq_tuples M H _ _ _ _ _ _ hZ,←mul_assoc]
  change ‖polynomial (data.character u) true W (Z^r) σ freq*↑(Z^(-(∑i,ell i)/2))*
    (∑p∈Fintype.piFinset T,A p*star (CanonicalRowCompletion.idealRowHom u (∏i,p i)))‖=_
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [originalTotal_supported_source _ _ _
    (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd)]

omit [NeZero M] in
theorem live_tuple_injective {ι : Type*} [Fintype ι]
    (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) : Function.Injective p := by
  intro i j he
  by_contra hij
  have hi := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hj := livePrime_data M H (V j) (a j) (b j) (Z^(ell j))
    (Real.rpow_pos_of_pos hZ _) (hV j) (p j) (Fintype.mem_piFinset.mp hp j)
  rw [he] at hi
  rcases hsep i j hij with h|h <;> linarith [hi.2.2.1,hi.2.2.2,hj.2.2.1,hj.2.2.2]

omit [NeZero M] in
theorem live_tuple_admissible {ι : Type*} [Fintype ι]
    (data : RowData) (V : ι→ℝ→ℂ) (a b ell : ι→ℝ) (Z : ℝ) (hZ : 0<Z)
    (hV : ∀i x,V i x≠0 → x∈Set.Icc (a i) (b i))
    (hlarge : ∀i,((baseCharacter data).modulus.absNorm:ℝ)<a i*Z^(ell i))
    (hsep : ∀i j,i≠j → b i*Z^(ell i)<a j*Z^(ell j) ∨
      b j*Z^(ell j)<a i*Z^(ell i))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset
      (fun i=>livePrimes M H (V i) (b i) (Z^(ell i)))) :
    CanonicalQuadraticSieve.Admissible (∏i,p i) := by
  have hd i := livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
    (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
  have hs (i : ι) : CanonicalQuadraticSieve.Supported (p i) := by
    by_contra hn
    exact base_nonzero_prime data (p i) (hd i).1 ((hlarge i).trans_le (hd i).2.2.1)
      (fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd (p i) hn)
  have hi := live_tuple_injective M H V a b ell Z hZ hV hsep p hp
  have hsprod : CanonicalQuadraticSieve.Supported (∏i,p i) := by
    have hh (S : Finset ι) : CanonicalQuadraticSieve.Supported (∏i∈S,p i) := by
      induction S using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
      | @insert i S hi ih =>
        rw [Finset.prod_insert hi]
        exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs i,ih⟩
    exact hh Finset.univ
  refine ⟨hsprod.1,?_,?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime (hd i).1).isMaximal (hd i).1.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime (hd j).1).isMaximal (hd j).1.ne_zero
      exact (Ideal.isCoprime_of_isMaximal (hi.ne hij)).isRelPrime
    · intro i _
      exact (hd i).1.squarefree
  · intro P hP
    exact hsprod.2 P hP

end SevenEighths.InverseInitialPhysicalSlots

end

end OAI
