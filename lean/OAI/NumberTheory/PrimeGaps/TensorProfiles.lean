import OAI.NumberTheory.PrimeGaps.CumulativeProfiles

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

theorem cumulativeProfile_budget {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n tau) : HasBudget (cumulativeProfile tau f) tau := by
  intro v hv hsum
  rw [cumulativeProfile_tail tau f hf v hv]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  by_contra hne
  have hh := hf (subset_tsupport f hne)
  have he : tau≤coordinateSum y :=
    hsum.le.trans (Finset.sum_le_sum (fun i _ => hy i))
  exact (not_lt_of_ge he) hh.2

theorem cumulativeProfile_signed_full {n : ℕ} (tau : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0≤v i) :
    signedDirections (coordinateDirectionList (Fin n))
      (fun y : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f y.ofLp:ℂ)) v =
      (f v.ofLp:ℂ) := by
  have hfc : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    (hf.comp_isClosedEmbedding (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph.isClosedEmbedding).comp_left
      Complex.ofReal_zero
  have hF : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hfs.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)
  have hT : ∀ y∈tsupport (fun y : EuclideanSpace ℝ (Fin n) => (f y.ofLp:ℂ)),
      ∀ i, y i≤tau := by
    intro y hy i
    have hsub := tsupport_comp_subset (g := (Complex.ofReal : ℝ → ℂ)) Complex.ofReal_zero
      (fun y : EuclideanSpace ℝ (Fin n) => f y.ofLp)
    have hp := tsupport_comp_subset_preimage f (EuclideanSpace.equiv (Fin n) ℝ).continuous
    exact profile_coordinate_upper hsupp y.ofLp (hp (hsub hy)) i
  have hh := complexCumulativeExtension_signed_full n tau _ hfc hF hT v hv
  rw [complexCumulativeExtension_ofReal] at hh
  convert hh using 1
  congr 2

noncomputable def appendMeasurableEquiv (n m : ℕ) :
    ((Fin n → ℝ) × (Fin m → ℝ)) ≃ᵐ (Fin (n+m) → ℝ) :=
  (Fin.appendHomeomorph n m).toMeasurableEquiv

@[simp] theorem appendMeasurableEquiv_apply (n m : ℕ) (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    appendMeasurableEquiv n m p = Fin.append p.1 p.2 := rfl

theorem appendMeasurableEquiv_measurePreserving (n m : ℕ) :
    MeasurePreserving (appendMeasurableEquiv n m) := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv)
  have he : appendMeasurableEquiv n m=e := by
    ext p i
    change Fin.append p.1 p.2 i = e p i
    cases i using Fin.addCases with
    | left i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
    | right i => simp [e,MeasurableEquiv.coe_piCongrLeft,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm,Equiv.piCongrLeft]
  rw [he]
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (n+m) => ℝ) finSumFinEquiv).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin m => ℝ))

noncomputable def tensorProfile {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin (n+m) → ℝ) : ℝ :=
  f (fun i => v (i.castAdd m)) * g (fun i => v (i.natAdd n))

@[simp] theorem tensorProfile_append {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    tensorProfile f g (Fin.append v w)=f v*g w := by
  simp [tensorProfile]

theorem tensorProfile_compact {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (tensorProfile f g) := by
  have hk : IsCompact ((tsupport f) ×ˢ (tsupport g)) := hf.isCompact.prod hg.isCompact
  have hh : HasCompactSupport (fun p : (Fin n → ℝ) × (Fin m → ℝ) => f p.1*g p.2) := by
    apply hk.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hk.isClosed
    intro p hp
    have hm := mul_ne_zero_iff.mp hp
    exact ⟨subset_tsupport f hm.1,subset_tsupport g hm.2⟩
  exact hh.comp_isClosedEmbedding (Fin.appendHomeomorph n m).symm.isClosedEmbedding

theorem tensorProfile_smooth {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (tensorProfile f g) := by
  unfold tensorProfile
  exact (hf.comp (contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (i.castAdd m)))).mul
    (hg.comp (contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (i.natAdd n))))

theorem tensorProfile_tsupport {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b) :
    tsupport (tensorProfile f g) ⊆ positiveSimplex (n+m) (a+b) := by
  intro v hv
  have hleft : (fun i : Fin n => v (i.castAdd m)) ∈ tsupport f := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin n => x (i.castAdd m)) f
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_left hv)
  have hright : (fun i : Fin m => v (i.natAdd n)) ∈ tsupport g := by
    exact tsupport_comp_subset_preimage (f := fun x : Fin (n+m) → ℝ =>
      fun i : Fin m => x (i.natAdd n)) g
      (continuous_pi (fun i => continuous_apply _)) (tsupport_mul_subset_right hv)
  refine ⟨?_,?_⟩
  · intro i
    cases i using Fin.addCases with
    | left i => exact (hf hleft).1 i
    | right i => exact (hg hright).1 i
  · change (∑ i, v i)<a+b
    rw [Fin.sum_univ_add]
    exact add_lt_add (hf hleft).2 (hg hright).2

theorem tensorProfile_tail {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ) :
    (∫ y in Ici (Fin.append v w), tensorProfile f g y) =
      (∫ y in Ici v, f y)*(∫ y in Ici w, g y) := by
  have hd : (appendMeasurableEquiv n m) ⁻¹' Ici (Fin.append v w) = (Ici v) ×ˢ (Ici w) := by
    ext p
    change (∀ i, Fin.append v w i≤Fin.append p.1 p.2 i) ↔ _
    constructor
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
  have hm := (appendMeasurableEquiv_measurePreserving n m).setIntegral_preimage_emb
    (appendMeasurableEquiv n m).measurableEmbedding (tensorProfile f g) (Ici (Fin.append v w))
  rw [hd] at hm
  rw [← hm]
  simp only [appendMeasurableEquiv_apply,tensorProfile_append]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_mul f g

theorem cumulativeProfile_tensor {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b)
    (v : Fin n → ℝ) (w : Fin m → ℝ) (hv : ∀ i, 0≤v i) (hw : ∀ i, 0≤w i) :
    cumulativeProfile (a+b) (tensorProfile f g) (Fin.append v w) =
      cumulativeProfile a f v*cumulativeProfile b g w := by
  rw [cumulativeProfile_tail (a+b) _ (tensorProfile_tsupport f g hf hg),
    cumulativeProfile_tail a f hf _ hv,cumulativeProfile_tail b g hg _ hw,tensorProfile_tail]
  intro i
  cases i using Fin.addCases with
  | left i => simpa using hv i
  | right i => simpa using hw i

@[simp] theorem logCoordinates_append (X : ℕ) {n m : ℕ}
    (d : Fin n → ℕ) (e : Fin m → ℕ) :
    logCoordinates X (Fin.append d e)=Fin.append (logCoordinates X d) (logCoordinates X e) := by
  ext i
  cases i using Fin.addCases <;> simp [logCoordinates]

@[simp] theorem divisorCoefficient_tensor (X : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (d : Fin n → ℕ) (e : Fin m → ℕ) :
    divisorCoefficient X (tensorProfile F G) (Fin.append d e)=
      divisorCoefficient X F d*divisorCoefficient X G e := by
  simp only [divisorCoefficient,logCoordinates_append,tensorProfile_append,Fin.prod_univ_add,
    Fin.append_left,Fin.append_right]
  ring

theorem divisorSum_tensor (X M : ℕ) {n m : ℕ}
    (F : (Fin n → ℝ) → ℝ) (G : (Fin m → ℝ) → ℝ) (b : Fin n → ℕ) (c : Fin m → ℕ) :
    divisorSum X (tensorProfile F G) M (Fin.append b c)=
      divisorSum X F M b*divisorSum X G M c := by
  classical
  unfold divisorSum
  rw [Finset.sum_mul_sum, ←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.appendEquiv n m)
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.appendEquiv_apply]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.addCases with
      | left i => simpa using h1 i
      | right i => simpa using h2 i
    · intro h
      exact ⟨fun i => by simpa using h (i.castAdd m),fun i => by simpa using h (i.natAdd n)⟩
  · intro p _
    exact (divisorCoefficient_tensor X F G p.1 p.2).symm

theorem divisorSum_congr_orthant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ℕ} (hX : 2≤X) (M : ℕ) (b : ι → ℕ) (F G : (ι → ℝ) → ℝ)
    (hFG : ∀ v, (∀ i, 0≤v i) → F v=G v) : divisorSum X F M b=divisorSum X G M b := by
  apply Finset.sum_congr rfl
  intro d hd
  unfold divisorCoefficient
  congr 1
  apply hFG
  apply logCoordinates_nonneg hX
  intro i
  exact Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i)

theorem divisorSum_cumulative_tensor {n m : ℕ} {a b : ℝ}
    (f : (Fin n → ℝ) → ℝ) (g : (Fin m → ℝ) → ℝ)
    (hf : tsupport f ⊆ positiveSimplex n a) (hg : tsupport g ⊆ positiveSimplex m b)
    {X : ℕ} (hX : 2≤X) (M : ℕ) (s : Fin n → ℕ) (t : Fin m → ℕ) :
    divisorSum X (cumulativeProfile (a+b) (tensorProfile f g)) M (Fin.append s t)=
      divisorSum X (cumulativeProfile a f) M s*divisorSum X (cumulativeProfile b g) M t := by
  rw [←divisorSum_tensor]
  apply divisorSum_congr_orthant hX
  intro v hv
  let v1 : Fin n → ℝ := fun i => v (i.castAdd m)
  let v2 : Fin m → ℝ := fun i => v (i.natAdd n)
  have he : v=Fin.append v1 v2 := by ext i; cases i using Fin.addCases <;> simp [v1,v2]
  rw [he,tensorProfile_append]
  exact cumulativeProfile_tensor f g hf hg v1 v2 (fun i => hv _) (fun i => hv _)

@[simp] theorem logCoordinates_snoc (X : ℕ) {n : ℕ} (d : Fin n → ℕ) (e : ℕ) :
    logCoordinates X (Fin.snoc d e) = Fin.snoc (logCoordinates X d) (Real.log e/Real.log X) := by
  ext i
  cases i using Fin.lastCases <;> simp [logCoordinates]

theorem divisorCoefficient_snoc_one (X : ℕ) {n : ℕ}
    (F : (Fin (n+1) → ℝ) → ℝ) (d : Fin n → ℕ) :
    divisorCoefficient X F (Fin.snoc d 1)=
      divisorCoefficient X (fun v => F (Fin.snoc v 0)) d := by
  simp [divisorCoefficient,logCoordinates_snoc,Fin.prod_univ_castSucc]

theorem divisorCoefficient_snoc_prime_zero {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (F : (Fin (n+1) → ℝ) → ℝ) {rho : ℝ} (hrho : rho<1) (hb : HasBudget F rho)
    (d : Fin n → ℕ) (hd : ∀ i, 0<d i) : divisorCoefficient X F (Fin.snoc d (M+a))=0 := by
  have hp : 0<M+a := by omega
  have hcoord := logCoordinates_nonneg hX (d := Fin.snoc d (M+a)) (by
    intro i; cases i using Fin.lastCases <;> simp [hp,hd])
  have hs : rho<∑ i,logCoordinates X (Fin.snoc d (M+a)) i := by
    apply hrho.trans
    apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _ => hcoord i) (Finset.mem_univ (Fin.last n)))
    simp only [logCoordinates,Fin.snoc_last]
    apply (lt_div_iff₀ (log_pos_of_two_le hX)).mpr
    simpa only [one_mul] using Real.log_lt_log (by exact_mod_cast (by omega : 0<X))
      (by exact_mod_cast hM)
  rw [divisorCoefficient,hb _ hcoord hs,mul_zero]

theorem divisorSum_snoc (X M : ℕ) {n : ℕ} (F : (Fin (n+1) → ℝ) → ℝ)
    (b : Fin n → ℕ) (a : ℕ) :
    divisorSum X F M (Fin.snoc b a)=
      ∑ r∈(M+a).divisors, ∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
        divisorCoefficient X F (Fin.snoc d r) := by
  classical
  unfold divisorSum
  rw [←Finset.sum_product']
  symm
  apply Finset.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => ℕ))
  · intro p
    simp only [Finset.mem_product,Fintype.mem_piFinset,Fin.snocEquiv]
    constructor
    · rintro ⟨h1,h2⟩ i
      cases i using Fin.lastCases with
      | last => simpa using h1
      | cast i => simpa using h2 i
    · intro h
      exact ⟨by simpa using h (Fin.last n),fun i => by simpa using h i.castSucc⟩
  · intro p _
    rfl

theorem divisorSum_prime_delete {X M a n : ℕ} (hX : 2≤X) (hM : X<M+a)
    (hp : Nat.Prime (M+a)) (F : (Fin (n+1) → ℝ) → ℝ)
    {rho : ℝ} (hrho : rho<1) (hb : HasBudget F rho) (b : Fin n → ℕ) :
    divisorSum X F M (Fin.snoc b a)=divisorSum X (fun v => F (Fin.snoc v 0)) M b := by
  rw [divisorSum_snoc,hp.divisors]
  rw [Finset.sum_insert (by simpa using hp.ne_one.symm),Finset.sum_singleton]
  have hz : (∑ d∈Fintype.piFinset (fun i => (M+b i).divisors),
      divisorCoefficient X F (Fin.snoc d (M+a)))=0 := by
    apply Finset.sum_eq_zero
    intro d hd
    exact divisorCoefficient_snoc_prime_zero hX hM F hrho hb d
      (fun i => Nat.pos_of_mem_divisors ((Fintype.mem_piFinset.mp hd) i))
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro d _
  exact divisorCoefficient_snoc_one X F d

@[simp] theorem fiberRay_apply {ι α : Type*} [Fintype ι]
    (b : ι → α) (r : α) (i : ι) : fiberRay b r i=if b i=r then 1 else 0 := by
  classical
  simp [fiberRay,WithLp.ofLp_sum,Finset.sum_apply]

theorem rayVector_fiber_nonneg {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (y : doubleFibers b R → ℝ) (hy : ∀ r, 0≤y r) (i : ι) :
    0≤rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i := by
  classical
  simp only [rayVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,fiberRay_apply]
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (hy r) (by split_ifs <;> norm_num))

theorem rayVector_singleton_zero {ι α : Type*} [Fintype ι]
    (b : ι → α) (R : Finset α) (i : ι)
    (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (y : doubleFibers b R → ℝ) :
    rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i=0 := by
  classical
  simp only [rayVector,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,fiberRay_apply]
  apply Finset.sum_eq_zero
  intro r _
  have hr : b i≠r.val := by
    intro he
    have hh := (Finset.mem_filter.mp r.property).2
    rw [←he,hi] at hh
    norm_num at hh
  simp [hr]

theorem cumulativeProfile_kernel_small_fibers {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
      (fun v => (cumulativeProfile tau f v.ofLp:ℂ)) hF hFs) (fiberSubsetFamily b R) =
      ∫ y, (f (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y).ofLp:ℂ)
        ∂positiveOrthantMeasure (doubleFibers b R) := by
  rw [small_fiber_kernelConstant b R hR hcard]
  apply integral_congr_ae
  rw [positiveOrthantMeasure_eq_restrict]
  filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
  exact cumulativeProfile_signed_full tau f hf hfs hsupp _
    (rayVector_fiber_nonneg b R y (fun r => (hy r (Set.mem_univ r)).le))

theorem cumulativeProfile_kernel_singleton_zero {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    {α : Type*} (b : Fin n → α) (R : Finset α) (hR : ∀ i,b i∈R)
    (hcard : ∀ r∈R, (Finset.univ.filter fun i => b i=r).card≤2)
    (i : Fin n) (hi : (Finset.univ.filter fun j => b j=b i).card=1)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (cumulativeProfile tau f v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin n))
      (fun v => (cumulativeProfile tau f v.ofLp:ℂ)) hF hFs) (fiberSubsetFamily b R)=0 := by
  rw [cumulativeProfile_kernel_small_fibers f hf hfs hsupp b R hR hcard]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  have hz : f (rayVector (fun r : doubleFibers b R => fiberRay b r.val) y).ofLp=0 := by
    by_contra hne
    have hh := (hsupp (subset_tsupport f hne)).1 i
    have he := rayVector_singleton_zero b R i hi y
    change 0<rayVector (fun r : doubleFibers b R => fiberRay b r.val) y i at hh
    rw [he] at hh
    exact lt_irrefl _ hh
  simp [hz]

@[simp] theorem append_self_addNat {n : ℕ} {α : Type*} (y z : Fin n → α) (i : Fin n) :
    Fin.append y z (i.addNat n)=z i := by
  rw [←Fin.natAdd_eq_addNat,Fin.append_right]

def duplicateLabels (n : ℕ) : Fin (n+n) → Fin n := Fin.append id id

theorem duplicateLabels_fiber_sum {n : ℕ} (r : Fin n) {K : Type*} [AddCommMonoid K]
    (w : Fin (n+n) → K) :
    (∑ i∈Finset.univ.filter (fun i => duplicateLabels n i=r), w i)=w (r.castAdd n)+w (r.natAdd n) := by
  classical
  rw [Finset.sum_filter,Fin.sum_univ_add]
  simp [duplicateLabels]

@[simp] theorem duplicateLabels_fiber_card {n : ℕ} (r : Fin n) :
    (Finset.univ.filter fun i => duplicateLabels n i=r).card=2 := by
  simpa using duplicateLabels_fiber_sum r (fun _ => (1:ℕ))

theorem duplicateLabels_classical_fiber {n : ℕ} (r : Fin n) :
    @Finset.filter (Fin (n+n)) (fun i => duplicateLabels n i=r)
      (fun _ => Classical.propDecidable _) Finset.univ =
      Finset.univ.filter (fun i => duplicateLabels n i=r) := by
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem duplicateLabels_kernel (n : ℕ) (w : Fin (n+n) → ℂ) :
    familyKernel (fiberSubsetFamily (duplicateLabels n) Finset.univ) w =
      (∏ i,w i)*(∏ i : Fin n,(w (i.castAdd n)+w (i.natAdd n))⁻¹) := by
  rw [familyKernel_small_fibers (duplicateLabels n) Finset.univ (fun i => Finset.mem_univ _) (by
    intro r _
    rw [duplicateLabels_classical_fiber,duplicateLabels_fiber_card])]
  simp only [duplicateLabels_classical_fiber,duplicateLabels_fiber_card,Finset.filter_true,
    duplicateLabels_fiber_sum]

noncomputable def duplicateRay {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin (n+n)) :=
  EuclideanSpace.single (i.castAdd n) 1+EuclideanSpace.single (i.natAdd n) 1

theorem duplicateRay_frequency {n : ℕ} (i : Fin n) (u : EuclideanSpace ℝ (Fin (n+n))) :
    laplaceFrequency (fourierCoordinateSum (Fin (n+n))) (duplicateRay i) u =
      frequencyW (u (i.castAdd n))+frequencyW (u (i.natAdd n)) := by
  unfold duplicateRay
  simp only [laplaceFrequency,map_add,inner_add_right,Complex.ofReal_add,
    fourierCoordinateSum_apply]
  simp [frequencyW,EuclideanSpace.inner_single_right]
  ring

theorem duplicateRay_positive {n : ℕ} (i : Fin n) :
    0<fourierCoordinateSum (Fin (n+n)) (duplicateRay i) := by
  have h := congrArg Complex.re (duplicateRay_frequency i 0)
  simp only [laplaceFrequency_re,Complex.add_re,frequencyW_re] at h
  rw [h]
  norm_num

theorem castAdd_ne_addNat_self {n : ℕ} (i j : Fin n) : i.castAdd n ≠ j.addNat n := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd,Fin.val_addNat] at hval
  omega

theorem addNat_ne_castAdd_self {n : ℕ} (i j : Fin n) : i.addNat n ≠ j.castAdd n :=
  (castAdd_ne_addNat_self j i).symm

theorem rayVector_duplicate {n : ℕ} (y : Fin n → ℝ) :
    (rayVector duplicateRay y).ofLp=Fin.append y y := by
  classical
  ext i
  cases i using Fin.addCases with
  | left i => simp [rayVector,duplicateRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,castAdd_ne_addNat_self]
  | right i => simp [rayVector,duplicateRay,WithLp.ofLp_sum,Finset.sum_apply,
      smul_eq_mul,Pi.single_apply,Finset.sum_add_distrib,addNat_ne_castAdd_self]

theorem duplicate_kernelConstant {n : ℕ}
    (F : EuclideanSpace ℝ (Fin (n+n)) → ℂ) (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n))) F hF hFs)
      (fiberSubsetFamily (duplicateLabels n) Finset.univ) =
      ∫ y, signedDirections (coordinateDirectionList (Fin (n+n))) F (rayVector duplicateRay y)
        ∂positiveOrthantMeasure (Fin n) := by
  rw [←sourceFourier_derivative_laplace (fourierCoordinateSum (Fin (n+n)))
    (coordinateDirectionList (Fin (n+n))) F hF hFs duplicateRay duplicateRay_positive]
  unfold kernelConstant
  apply integral_congr_ae
  filter_upwards [] with u
  rw [contourKernel,duplicateLabels_kernel,coordinateDirectionList_multiplier]
  simp only [duplicateRay_frequency,mul_assoc]

theorem cumulative_tensor_diagonal_kernel {n : ℕ} {tau : ℝ}
    (f : (Fin n → ℝ) → ℝ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ positiveSimplex n tau)
    (hF : HasCompactSupport (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)))
    (hFs : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
      (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ))) :
    kernelConstant (sourceFourier (fourierCoordinateSum (Fin (n+n)))
      (fun v => (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) hF hFs)
      (fiberSubsetFamily (duplicateLabels n) Finset.univ) = (l2Mass f:ℂ) := by
  rw [duplicate_kernelConstant]
  have he : (∫ y, signedDirections (coordinateDirectionList (Fin (n+n)))
      (fun v : EuclideanSpace ℝ (Fin (n+n)) =>
        (cumulativeProfile (tau+tau) (tensorProfile f f) v.ofLp:ℂ)) (rayVector duplicateRay y)
      ∂positiveOrthantMeasure (Fin n)) =
      ∫ y, (f y^2:ℂ) ∂positiveOrthantMeasure (Fin n) := by
    apply integral_congr_ae
    rw [positiveOrthantMeasure_eq_restrict]
    filter_upwards [ae_restrict_mem (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioi))] with y hy
    rw [cumulativeProfile_signed_full (tau+tau) (tensorProfile f f)
      (tensorProfile_compact f f hf hf) (tensorProfile_smooth f f hfs hfs)
      (tensorProfile_tsupport f f hsupp hsupp)]
    · rw [rayVector_duplicate,tensorProfile_append,pow_two]
      simp only [Complex.ofReal_mul]
    · intro i
      rw [rayVector_duplicate]
      cases i using Fin.addCases with
      | left i => simpa using (hy i (Set.mem_univ i)).le
      | right i => simpa using (hy i (Set.mem_univ i)).le
  rw [he]
  simp_rw [←Complex.ofReal_pow]
  rw [integral_complex_ofReal,positiveOrthantMeasure_eq_restrict]
  congr 1
  unfold l2Mass
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfz : f y=0 := by
    by_contra hne
    exact hy (fun i _ => (hsupp (subset_tsupport f hne)).1 i)
  simp [hfz]

end LargePrimeGaps

end OAI
