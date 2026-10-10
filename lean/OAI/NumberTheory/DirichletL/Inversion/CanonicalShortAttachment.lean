import OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool
import OAI.NumberTheory.DirichletL.Descent.CompletionSplit
import OAI.NumberTheory.DirichletL.Descent.ReopenedBins
import OAI.NumberTheory.DirichletL.Inversion.ShortCanonicalNormalization

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseCanonicalShortAttachment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis" => ActualEisensteinCubic.O
universe u v

def idealLists {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (j : σ) : Finset (Ideal Eis) :=
  (lists j).image Subtype.val

def transportCoeff {σ : Type u} (F : Finset (Ideal Eis))
    (a : σ→primePool F→ℂ) (j : σ) (P : Ideal Eis) : ℂ :=
  if h:P∈primePool F then a j ⟨P,h⟩ else 0

@[simp] theorem transportCoeff_val {σ : Type u} (F : Finset (Ideal Eis))
    (a : σ→primePool F→ℂ) (j : σ) (i : primePool F) :
    transportCoeff F a j i.val=a j i := by simp [transportCoeff]

def idealWeights {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (j : σ) (P : idealLists F lists j) : ℂ := transportCoeff F a j P.val

lemma tuple_mark_product {σ : Type u} [Fintype σ] [DecidableEq σ]
    (lists : σ→Finset (Ideal Eis)) (w : ∀j,lists j→ℂ) (A : Ideal Eis) :
    tupleDivisibilityMark lists w A=
      ∏j,∑P:lists j,if P.val∣A then w j P else 0 := by
  unfold tupleDivisibilityMark
  calc
    _ = ∑p:∀j,lists j,∏j,if (p j).val∣A then w j (p j) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      split_ifs <;> simp
    _ = _ := (Fintype.prod_sum (fun j (P : lists j)=>if P.val∣A then w j P else 0)).symm

theorem indexed_mark_eq_tuple {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal Eis)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (a : σ→primePool F→ℂ) (A : Ideal Eis) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a A=
      tupleDivisibilityMark (fun j:slots=>idealLists F lists j.val)
        (fun j:slots=>idealWeights F lists a j.val) A := by
  rw [tuple_mark_product]
  unfold indexedIdealMark
  rw [←Finset.prod_coe_sort slots]
  apply Finset.prod_congr rfl
  intro j hj
  change _ = ∑P:idealLists F lists j.val,if P.val∣A then transportCoeff F a j.val P.val else 0
  rw [Finset.sum_coe_sort (idealLists F lists j.val) (fun P : Ideal Eis=>if P∣A then transportCoeff F a j.val P else 0)]
  change (∑i∈lists j.val,if i.val∣A then a j.val i else 0)=
    ∑P∈(lists j.val).image Subtype.val,if P∣A then transportCoeff F a j.val P else 0
  rw [Finset.sum_image (fun i hi k hk h=>Subtype.ext h)]
  simp only [transportCoeff_val]

lemma idealLists_disjoint {σ : Type u} [DecidableEq σ]
    (F : Finset (Ideal Eis)) (slots : Finset σ) (lists : σ→Finset (primePool F))
    (h : (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k))) :
    Pairwise (fun j k:slots=>Disjoint (idealLists F lists j.val) (idealLists F lists k.val)) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hP
  obtain ⟨i',hi',he'⟩:=Finset.mem_image.mp hQ
  have hii : i=i' := Subtype.ext (he.trans he'.symm)
  have hjk' : j.val≠k.val := fun he=>hjk (Subtype.ext he)
  exact Finset.disjoint_left.mp (h j.property k.property hjk') hi (hii.symm ▸ hi')

lemma idealLists_prime_data {σ : Type u} (F : Finset (Ideal Eis))
    (hF : ∀I∈F,Admissible I) (lists : σ→Finset (primePool F))
    (j : σ) (P : Ideal Eis) (hP : P∈idealLists F lists j) :
    P.IsMaximal ∧ goodLambda∉P ∧ Prime P ∧ ringChar (Eis⧸P)≠2 := by
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
  refine ⟨inferInstance,poolGood F hF i,?_,poolOdd F hF i⟩
  exact Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance

lemma idealLists_capacity {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (H : σ→ℝ)
    (hH : ∀j,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤H j) :
    ∀j,∀P∈idealLists F lists j,(Ideal.absNorm P:ℝ)≤H j := by
  intro j P hP
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
  exact hH j i hi

lemma idealWeights_norm {σ : Type u} (F : Finset (Ideal Eis))
    (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (ha : ∀j,∀i∈lists j,‖a j i‖≤1) :
    ∀j,∀P:idealLists F lists j,‖idealWeights F lists a j P‖≤1 := by
  intro j P
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp P.property
  change ‖transportCoeff F a j P.val‖≤1
  rw [←he,transportCoeff_val]
  exact ha j i hi

def longReopened (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (mark : Ideal Eis→ℂ) : ℂ :=
  ∑' I:Ideal Eis,∑' B:Ideal Eis,largeCubeCoefficient H₀ B*summand Ψ W X I B*mark (I*B^3)

theorem complete_pool_split {σ : Type u} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (Ψ : Eis→*ℂ) (m f k : Eis) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀x,W x≠0→x≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let mark:=indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    let row:=rowTwist Ψ (m*excludedGenerator S) f k
    outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X=
      (Real.sqrt X:ℂ)*(markedShortCompletedSum row W X H₀ mark+longReopened row W X H₀ mark) := by
  dsimp only
  have hg:=finiteCanonicalMarkedRow_complete_global S D hbad hSp Ψ m f k W b X hX hW hD slots lists a
  change outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X=_ at hg
  have he:=marked_completed_cube_inverse_split (rowTwist Ψ (m*excludedGenerator S) f k)
    W hWc X H₀ hX
    (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)
  rw [←hg] at he
  change (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X=
    markedShortCompletedSum _ W X H₀ _+longReopened _ W X H₀ _ at he
  have hn : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  calc
    _ = (Real.sqrt X:ℂ)*((Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X) := by rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
    _ = _ := by rw [he]

lemma complete_pool_sub_long {σ : Type u} [DecidableEq σ]
    (S : Finset (Ideal Eis)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (Ψ : Eis→*ℂ) (m f k : Eis) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀x,W x≠0→x≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let mark:=indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    let row:=rowTwist Ψ (m*excludedGenerator S) f k
    outsideCanonicalMarkedRow S D hbad Ψ m f k slots lists a W X-
      (Real.sqrt X:ℂ)*longReopened row W X H₀ mark=
      (Real.sqrt X:ℂ)*markedShortCompletedSum row W X H₀ mark := by
  dsimp only
  rw [complete_pool_split S D hbad hSp Ψ m f k W hWc b X H₀ hX hW hD slots lists a]
  ring

lemma primary_span (f : Ideal Eis) (hf : Supported f) : Ideal.span {primaryGenerator f}=f :=
  (primaryGenerator_spec f (supported_primaryGenerator_ne_zero f hf)).1

lemma actual_mask (q : ℕ) (m : Eis) :
    m*excludedGenerator (reflectionExcludedPrimes q)=ActualFiber.maskElement q m := rfl

theorem normalized_complete_short_attachment (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [DecidableEq σ],
    ∀ (m : Eis),m≠0 → ∀ (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hcut≤d+eta → d≤cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀f∈labels,Supported f ∧ Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
    ∀ D : ℕ,hi*Z^N≤D → ∀ slots : Finset σ,slots.card≤rmax →
    ∀ (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H : σ→ℝ),
      (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k)) →
      (∀j∈slots,1≤H j) → (∀j∈slots,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤H j) →
      (∏j∈slots,H j)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ)
      (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀j∈slots,∀i∈lists j,‖a j i‖≤1) →
      let S:=reflectionExcludedPrimes q
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let mark:=indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      (∑f∈labels,secondLabelWeight K f*∑k∈T,
        ‖((Z^(-(N+V)/2):ℝ):ℂ)*
          (outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (primaryGenerator f) k
            slots lists a (normTwistedSource W θ) (Z^N)-
            (Real.sqrt (Z^N):ℂ)*longReopened
              (rowTwist Ψ (ActualFiber.maskElement q m) (primaryGenerator f) k)
              (normTwistedSource W θ) (Z^N) (Z^hcut) mark)‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩:=InverseShortCanonicalNormalization.canonical_short_normalized_generator_energy
    q hq lo hi hlo W hWs hW L cstar eta hL hcstar heta heta1 hetac rmax K
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels hlabels T hT D hD slots hcard lists H hdis hH1 hH hprod
    Ψ hΨ hperiod θ a ha
  dsimp only
  let S:=reflectionExcludedPrimes q
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF : ∀I∈F,Admissible I:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
  let ilists:slots→Finset (Ideal Eis):=fun j=>idealLists F lists j.val
  let iw:∀j,ilists j→ℂ:=fun j=>idealWeights F lists a j.val
  have hp (j:slots) (P:Ideal Eis) (hP:P∈ilists j) := idealLists_prime_data F hF lists j.val P hP
  have hcap : ∀j:slots,∀P∈ilists j,(Ideal.absNorm P:ℝ)≤H j.val := by
    intro j P hP
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hP
    exact hH j.val j.property i hi
  have hw : ∀j:slots,∀P:ilists j,‖iw j P‖≤1 := by
    intro j P
    obtain ⟨i,hi,hh⟩:=Finset.mem_image.mp P.property
    change ‖transportCoeff F a j.val P.val‖≤1
    rw [←hh,transportCoeff_val]
    exact ha j.val j.property i hi
  have henergy:=he (σ:=slots) m hm Z N V M z₀ margin hcut d hZ hN hV hM hMc hVc hzc hcut0 hcutc
    hRn hmargin hreserve hVd hcutd hd labels (fun f hf=>(hlabels f hf).2) primaryGenerator
    (fun f hf=>primary_span f (hlabels f hf).1) T hT (by simpa using hcard)
    ilists (fun j:slots=>H j.val) (idealLists_disjoint F slots lists hdis)
    (fun j P hP=>(hp j P hP).1) (fun j P hP=>(hp j P hP).2.1)
    (fun j P hP=>(hp j P hP).2.2.1) (fun j P hP=>(hp j P hP).2.2.2)
    (fun j=>hH1 j.val j.property) hcap (by simpa only [Finset.prod_coe_sort] using hprod)
    Ψ hΨ hperiod θ iw hw
  have hz : 0<Z:=zero_lt_one.trans (lt_of_lt_of_le hZ₀ hZ)
  have hX : 0<Z^N:=Real.rpow_pos_of_pos hz _
  have htw : HasCompactSupport (normTwistedSource W θ):=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((normTwistedSource_support W θ).trans hWs)
  have hupper : ∀x,normTwistedSource W θ x≠0→x≤hi := fun x hx=>
    (hWs (normTwistedSource_support W θ hx)).2
  have hmark : indexedIdealMark (fun i:primePool F=>i.val) slots lists a=
      tupleDivisibilityMark ilists iw := funext (indexed_mark_eq_tuple F slots lists a)
  have hsame (f : Ideal Eis) (k : Eis) :
      outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (primaryGenerator f) k
        slots lists a (normTwistedSource W θ) (Z^N)-
        (Real.sqrt (Z^N):ℂ)*longReopened
          (rowTwist Ψ (ActualFiber.maskElement q m) (primaryGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut)
          (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)=
      (Real.sqrt (Z^N):ℂ)*markedShortCompletedSum
        (rowTwist Ψ (ActualFiber.maskElement q m) (primaryGenerator f) k)
        (normTwistedSource W θ) (Z^N) (Z^hcut) (tupleDivisibilityMark ilists iw) := by
    have hh:=complete_pool_sub_long S D (reflectionExcludedPrimes_bad q)
      (reflectionExcludedPrimes_prime q) Ψ m (primaryGenerator f) k
      (normTwistedSource W θ) htw hi (Z^N) (Z^hcut) hX hupper hD slots lists a
    dsimp only at hh
    rw [actual_mask] at hh
    exact hh.trans (by rw [hmark])
  dsimp only [S, F] at hsame
  simp_rw [hsame]
  simpa only [mul_assoc] using henergy

end SevenEighths.InverseCanonicalShortAttachment

end

end OAI
