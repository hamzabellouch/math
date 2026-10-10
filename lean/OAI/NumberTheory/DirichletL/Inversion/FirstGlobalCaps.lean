import OAI.NumberTheory.DirichletL.Inversion.FirstGlobalParents
import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsLive
import OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsPhysical

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalCaps
open InverseMoment InverseFirstGlobalParents InverseFirstPriorityParents
open InverseMomentWholePriorityParents InverseMomentFirstChildWindows
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open ConcreteTraceCRT (eisEmbedding)
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def outerNorms (p : ι→O) (x : FirstOriginalOuter ι) : Fin 5→ℝ :=
  ![‖eisEmbedding (aLabel p x.1.support x.1.rightBit)‖^2,
    ‖eisEmbedding (aLabel p x.1.support x.1.leftBit)‖^2,
    primeProductNorm p x.2.1,
    ‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2,
    primeProductNorm p (cubeActiveSupport x.1.support
      (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)]

def outerGate (p : ι→O) (k : SourceIndex) (x : FirstOriginalOuter ι) : Prop :=
  ∀i : Fin 5,dyadIndex (outerNorms p x i)=k i.castSucc

def outerCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :=
  (firstOriginalOuter pool Q).filter (outerGate p k)

def parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ) :=
  (originalParentSource pool Q (fun x=>commonSelector p (selector x) l)).filter
    (fun x=>outerGate p k (toOriginal x))

theorem mem_parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (x : Source ι 0) : x∈parentCell p pool Q selector k l ↔
    ∃o∈outerCell p pool Q k,∃D∈pool.powerset,
      commonSelector p (selector o) l D≠0 ∧ fillFirstQuotient (ofOriginal o) D=x := by
  simp only [parentCell,outerCell,Finset.mem_filter,mem_originalParentSource]
  constructor
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hg⟩
    exact ⟨o,⟨ho,by simpa using hg⟩,D,hD,hs,rfl⟩
  · rintro ⟨o,⟨ho,hg⟩,D,hD,hs,rfl⟩
    exact ⟨⟨o,ho,D,hD,hs,rfl⟩,by simpa using hg⟩

def originalNorms (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O) : Fin 6→ℝ :=
  sourceNorms (fun y=>outerNorms p y.1 0) (fun y=>outerNorms p y.1 1)
    (fun y=>outerNorms p y.1 2) (fun y=>outerNorms p y.1 4)
    (fun y=>primeSubsetGenerator (fun i=>Ideal.span {p i}) y.1.2.2)
    (fun y=>y.2.2) x

lemma originalNorms_outer (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (i : Fin 5) : originalNorms p x i.castSucc=outerNorms p x.1 i := by
  fin_cases i <;> rfl

lemma originalNorms_frequency (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O) :
    originalNorms p x 5=‖eisEmbedding x.2.2‖^2 := rfl

theorem sourceCell_outer (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k) :
    x.1∈outerCell p pool Q k := by
  obtain ⟨hs,hk⟩:=Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_sigma.mp hs).1,?_⟩
  intro i
  simpa only [sourceIndex,originalNorms_outer] using congrFun hk i.castSucc

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerNorms_ge_one (x : FirstOriginalOuter ι) : ∀i,1≤outerNorms p x i := by
  intro i
  fin_cases i
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · change 1≤‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma source_norms_ge_one (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) :
    ∀i,1≤originalNorms p x i := by
  have hf:=((mem_firstRetainedSource p labels x.1.1 Y x.2).mp (Finset.mem_sigma.mp hx).2).2
  have hn : x.2.2≠0 := (Finset.mem_erase.mp hf).1
  intro i
  fin_cases i
  · exact outerNorms_ge_one p hp x.1 0
  · exact outerNorms_ge_one p hp x.1 1
  · exact outerNorms_ge_one p hp x.1 2
  · exact outerNorms_ge_one p hp x.1 3
  · exact outerNorms_ge_one p hp x.1 4
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hn

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem sourceCell_frequency (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k) :
    dyadScale (k 5)≤‖eisEmbedding x.2.2‖^2 ∧
      ‖eisEmbedding x.2.2‖^2≤2*dyadScale (k 5) := by
  have h:=sourceCell_ratios (originalNorms p) _ (source_norms_ge_one p hp pool Q labels Y) k x hx 5
  exact ⟨by simpa only [originalNorms_frequency,one_mul] using (le_div_iff₀ (dyadScale_pos _)).mp h.1,
    by simpa only [originalNorms_frequency] using (div_le_iff₀ (dyadScale_pos _)).mp h.2⟩

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerGate_dyads (k : SourceIndex) (x : FirstOriginalOuter ι) (hx : outerGate p k x) :
    ∀i : Fin 5,dyadScale (k i.castSucc)≤outerNorms p x i ∧
      outerNorms p x i≤2*dyadScale (k i.castSucc) := by
  intro i
  have h:=dyadIndex_bounds _ (outerNorms_ge_one p hp x i)
  rw [hx i] at h
  exact ⟨h.1,h.2.le⟩

omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma commonSelector_norm (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι) :
    ‖commonSelector p selector l D‖≤‖selector D‖ := by
  unfold commonSelector
  split_ifs <;> simp

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_common_dyads (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι)
    (hlive : commonSelector p selector l D≠0) :
    dyadScale l≤primeProductNorm p D ∧ primeProductNorm p D≤2*dyadScale l := by
  have he : dyadIndex (primeProductNorm p D)=l := by
    by_contra h
    exact hlive (by simp [commonSelector,h])
  have h:=dyadIndex_bounds _ (primeProductNorm_ge_one p hp D)
  rw [he] at h
  exact ⟨h.1,h.2.le⟩

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
lemma sourceIdeal_norm (D : Finset ι) : (Ideal.absNorm (sourceIdeal p D):ℝ)=primeProductNorm p D := by
  simp only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm]

omit [∀i,(Ideal.span {p i}).IsMaximal] in

theorem parentCell_cube_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z ell eta : ℝ)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  exact reopenedCubeFamily_cube_norms p Q _ hQ o.1
    ((mem_firstOriginalOuter pool Q o).mp (Finset.mem_filter.mp ho).1).1

def dyadicExponent (Z : ℝ) (n : ℕ) : ℝ := Real.logb Z (dyadScale n)

lemma rpow_dyadicExponent (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    Z^dyadicExponent Z n=dyadScale n :=
  Real.rpow_logb (by linarith) (by linarith) (dyadScale_pos n)

lemma dyad_power_bounds (Z eta q : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta) (n : ℕ)
    (hq : dyadScale n≤q ∧ q≤2*dyadScale n) :
    Z^dyadicExponent Z n≤q ∧ q≤Z^(dyadicExponent Z n+eta) := by
  rw [Real.rpow_add (by linarith),rpow_dyadicExponent Z hZ]
  refine ⟨hq.1,hq.2.trans ?_⟩
  nlinarith [dyadScale_pos n]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_norm_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (∀i : Fin 5,Z^dyadicExponent Z (k i.castSucc)≤outerNorms p (toOriginal x) i ∧
      outerNorms p (toOriginal x) i≤Z^(dyadicExponent Z (k i.castSucc)+eta)) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)=primeProductNorm p x.quotientSupport ∧
    Z^dyadicExponent Z l≤(Ideal.absNorm (parent p x).quotient:ℝ) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)≤Z^(dyadicExponent Z l+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  have hg := outerGate_dyads p hp k o (Finset.mem_filter.mp ho).2
  have hd := live_common_dyads p hp (selector o) l D hs
  simp only [toOriginal_fill,toOriginal_ofOriginal]
  refine ⟨fun i=>dyad_power_bounds Z eta _ hZ h2 _ (hg i),sourceIdeal_norm p D,?_⟩
  change Z^dyadicExponent Z l≤(Ideal.absNorm (sourceIdeal p D):ℝ) ∧
    (Ideal.absNorm (sourceIdeal p D):ℝ)≤Z^(dyadicExponent Z l+eta)
  rw [sourceIdeal_norm]
  exact dyad_power_bounds Z eta _ hZ h2 l hd

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_ideal_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (Z^dyadicExponent Z (k 2)≤primeProductNorm p x.firstCommon ∧
      primeProductNorm p x.firstCommon≤Z^(dyadicExponent Z (k 2)+eta)) ∧
    (Z^dyadicExponent Z (k 3)≤(Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ)≤Z^(dyadicExponent Z (k 3)+eta)) ∧
    (Z^dyadicExponent Z (k 4)≤(Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ)
        ≤Z^(dyadicExponent Z (k 4)+eta)) := by
  have h:=(parentCell_norm_bounds p hp pool Q selector k l Z eta hZ h2 x hx).1
  refine ⟨h 2,?_,?_⟩
  · simpa [sourceIdeal_norm,outerNorms,toOriginal,primeSubsetGenerator_norm_eq_productNorm] using h 3
  · simpa [sourceIdeal_norm,outerNorms,toOriginal] using h 4

def jNorm (p : ι→O) (x : FirstOriginalOuter ι) : ℝ :=
  ‖eisEmbedding (jLabel p x.1.support (fun i=>x.1.leftExponent i+x.1.rightExponent i)
    x.1.leftBit x.1.rightBit)‖^2

def labelParentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ) :=
  (parentCell p pool Q selector k l).filter (fun x=>dyadIndex (jNorm p (toOriginal x))=j)

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem labelParentCell_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈labelParentCell p pool Q selector k l j) :
    x∈parentCell p pool Q selector k l ∧
    Z^dyadicExponent Z j≤jNorm p (toOriginal x) ∧
      jNorm p (toOriginal x)≤Z^(dyadicExponent Z j+eta) := by
  obtain ⟨hm,hj⟩:=Finset.mem_filter.mp hx
  have hn : 1≤jNorm p (toOriginal x) :=
    EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  have hd:=dyadIndex_bounds _ hn
  rw [hj] at hd
  exact ⟨hm,dyad_power_bounds Z eta _ hZ h2 j ⟨hd.1,hd.2.le⟩⟩

theorem raw_column_exponent (Z r : ℝ) (hZ : 1<Z) (a b c : ℕ) :
    Z^r/(dyadScale a*dyadScale b*dyadScale c)=
      Z^(r-dyadicExponent Z a-dyadicExponent Z b-dyadicExponent Z c) := by
  simp only [Real.rpow_sub (show 0<Z by linarith),rpow_dyadicExponent Z hZ]
  simp only [div_div]

theorem columnScales_exponents (Z r : ℝ) (hZ : 1<Z) (k : SourceIndex) (l : ℕ) :
    columnScales k l (Z^r) (Z^r)=rawScales k l
      (Z^(r-dyadicExponent Z (k 0)-dyadicExponent Z (k 2)-dyadicExponent Z l))
      (Z^(r-dyadicExponent Z (k 1)-dyadicExponent Z (k 2)-dyadicExponent Z l)) := by
  simp only [columnScales,raw_column_exponent Z r hZ]

theorem columnScales_products (Z r : ℝ) (k : SourceIndex) (l : ℕ) :
    let s:=columnScales k l (Z^r) (Z^r)
    s 0*s 2*s 5*s 7=Z^r ∧ s 1*s 2*s 5*s 8=Z^r :=
  ⟨columnScales_left k l _ _,columnScales_right k l _ _⟩

theorem sourceCell_parent (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (l : ℕ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k)
    (D : Finset ι) (hD : D⊆pool) (hs : commonSelector p (selector x.1) l D≠0) :
    fillFirstQuotient (ofOriginal x.1) D∈parentCell p pool Q selector k l :=
  (mem_parentCell p pool Q selector k l _).mpr
    ⟨x.1,sourceCell_outer p pool Q labels Y k x hx,D,Finset.mem_powerset.mpr hD,hs,rfl⟩

theorem outerCell_eq_of_first_five (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k k' : SourceIndex) (h : ∀i : Fin 5,k i.castSucc=k' i.castSucc) :
    outerCell p pool Q k=outerCell p pool Q k' := by
  ext x
  simp only [outerCell, Finset.mem_filter, outerGate, h]

omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_selector_norm_le_one (selector : Finset ι→ℂ)
    (hs : ∀D,‖selector D‖≤1) (l : ℕ) (D : Finset ι) :
    ‖commonSelector p selector l D‖≤1 := (commonSelector_norm p selector l D).trans (hs D)

include hp in

theorem sourceCell_actual_ratios
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (Y : ℝ)
    (selector C₁ C₂ : (Σ _ : FirstOriginalOuter ι,Ideal O×O)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k)
    (j : FirstCommonIndex ι)
    (hn : commonSelector p (selector x) l j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j≠0) :
    ∀i,actualOuterRatios p (outerNorms p x.1 0) (outerNorms p x.1 1)
      (outerNorms p x.1 2) (outerNorms p x.1 4)
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) x.2.2 j (rawScales k l T₁ T₂) i∈Set.Icc 1 2 := by
  exact actual_original_cell_ratios p hp hg _ selector C₁ C₂
    (fun y=>outerNorms p y.1 0) (fun y=>outerNorms p y.1 1)
    (fun y=>outerNorms p y.1 2) (fun y=>outerNorms p y.1 4)
    (fun y=>primeSubsetGenerator (fun i=>Ideal.span {p i}) y.1.2.2) (fun y=>y.2.2)
    (source_norms_ge_one p hp pool Q labels Y) k l T₁ T₂ x hx j hn

end SevenEighths.InverseFirstGlobalCaps

end

end OAI
