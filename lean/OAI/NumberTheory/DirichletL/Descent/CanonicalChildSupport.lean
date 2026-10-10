import OAI.NumberTheory.DirichletL.Descent.FirstCanonicalChildren

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialArithmetic InverseSecondSourceBlocks InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
variable (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_prime_supported (i:ι):Supported (Ideal.span {p i}) :=by
  have hn:(Ideal.span {p i}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr (hp i)
  refine ⟨hn,?_⟩
  intro P hP
  obtain ⟨hprime,hle⟩:=(Ideal.mem_normalizedFactors_iff hn).mp hP
  have he:Ideal.span {p i}=P:=(inferInstance:(Ideal.span {p i}:Ideal O).IsMaximal).eq_of_le hprime.ne_top hle
  subst P
  exact ⟨hg i,hc i⟩

lemma canonical_supported_prod {α:Type*}(S:Finset α)(f:α→Ideal O)
    (hf:∀i∈S,Supported (f i)):Supported (∏i∈S,f i) :=by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Supported (1:Ideal O)
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,supported_mul_iff]
    exact ⟨hf i (Finset.mem_insert_self _ _),ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj))⟩

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_ideal_supported (S:Finset ι):Supported (sourceIdeal p S) :=by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact canonical_supported_prod S (fun i=>Ideal.span {p i}) (fun i _=>canonical_source_prime_supported p hp hg hc i)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_prime_product_supported (S:Finset ι)(v:ι→ℕ):Supported (Ideal.span {primeProduct p S v}) :=by
  rw [primeProduct,FiniteGaussPhase.span_finset_prod]
  apply canonical_supported_prod
  intro i hi
  rw [←Ideal.span_singleton_pow]
  exact supported_pow (canonical_source_prime_supported p hp hg hc i) _

include hp hg hc in
lemma actual_second_label_supported {Jo Jn:ℕ}(x:MarkedSecondSource ι Jo Jn):
    Supported (actualSecondChild p 1 1 x).2.1 :=by
  change Supported ((Ideal.span {jLabel p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit})*
    sourceIdeal p x.firstCommon*sourceIdeal p x.second.divisor*sourceIdeal p x.second.overlap)
  simp only [supported_mul_iff]
  exact ⟨⟨⟨canonical_prime_product_supported p hp hg hc _ _,canonical_source_ideal_supported p hp hg hc _⟩,
    canonical_source_ideal_supported p hp hg hc _⟩,canonical_source_ideal_supported p hp hg hc _⟩

include hp hg hc in
theorem actual_cell_labels_supported {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈actualCellLabels p S d,Supported I :=by
  intro I hI
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hI
  exact actual_second_label_supported p hp hg hc x

include hp hg hc in
theorem actual_cell_labels_admissible {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈(actualCellLabels p S d).filter Squarefree,CanonicalQuadraticSieve.Admissible I :=by
  intro I hI
  obtain ⟨hm,hs⟩:=Finset.mem_filter.mp hI
  have hh:=actual_cell_labels_supported p hp hg hc S d I hm
  exact ⟨hh.1,hs,hh.2⟩

end SevenEighths.InverseMoment

end

end OAI
