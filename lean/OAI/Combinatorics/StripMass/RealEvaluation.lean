import Mathlib
import OAI.Combinatorics.StripMass.ArchRoots

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset

def anglePhase (u : ℝ) : ℂ := Complex.exp ((u:ℂ)*Complex.I)

@[simp] lemma anglePhase_ne_zero (u : ℝ) : anglePhase u≠0 := Complex.exp_ne_zero _
@[simp] lemma anglePhase_zero : anglePhase 0=1 := by simp [anglePhase]
lemma anglePhase_add (u v : ℝ) : anglePhase (u+v)=anglePhase u*anglePhase v := by
  simp only [anglePhase,Complex.ofReal_add,add_mul,Complex.exp_add]
lemma anglePhase_neg (u : ℝ) : anglePhase (-u)=(anglePhase u)⁻¹ := by
  simp [anglePhase,Complex.exp_neg]
lemma anglePhase_sub (u v : ℝ) : anglePhase (u-v)=anglePhase u/anglePhase v := by
  simp only [sub_eq_add_neg,anglePhase_add,anglePhase_neg,div_eq_mul_inv]
lemma anglePhase_nat_mul (k : ℕ) (u : ℝ) : anglePhase ((k:ℝ)*u)=anglePhase u^k := by
  simp only [anglePhase,Complex.ofReal_mul,Complex.ofReal_natCast,←Complex.exp_nat_mul,mul_assoc]
lemma anglePhase_int_mul (k : ℤ) (u : ℝ) : anglePhase ((k:ℝ)*u)=anglePhase u^k := by
  simp only [anglePhase,Complex.ofReal_mul,Complex.ofReal_intCast,←Complex.exp_int_mul,mul_assoc]
lemma anglePhase_lambda : anglePhase lambda=phase := rfl
lemma anglePhase_sine (u : ℝ) : (anglePhase u-(anglePhase u)⁻¹)/(2*Complex.I)=(Real.sin u:ℂ) := by
  rw [anglePhase,Complex.ofReal_sin,Complex.sin,←Complex.exp_neg]
  field_simp
  simp [Complex.I_sq]
lemma anglePhase_cosine (u : ℝ) : (anglePhase u+(anglePhase u)⁻¹)/2=(Real.cos u:ℂ) := by
  rw [anglePhase,Complex.ofReal_cos,Complex.cos,←Complex.exp_neg]
  simp only [neg_mul]

def angleCharacter {n : ℕ} (u : Fin n → ℝ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun e := ∏ i,anglePhase (u i)^e.toAdd i
  map_one' := by simp
  map_mul' e f := by
    change (∏i,anglePhase (u i)^(e.toAdd i+f.toAdd i))=_
    simp only [zpow_add₀ (anglePhase_ne_zero _),prod_mul_distrib]

def angleEvaluation {n : ℕ} (u : Fin n → ℝ) : Laurent n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (angleCharacter u)

@[simp] lemma angleEvaluation_monomial {n : ℕ} (u : Fin n → ℝ) (e : Fin n → ℤ) (z : ℂ) :
    angleEvaluation u (monomialL e z)=z*∏i,anglePhase (u i)^e i := by
  simp [angleEvaluation,monomialL,AddMonoidAlgebra.lift_single,angleCharacter]
@[simp] lemma angleEvaluation_constant {n : ℕ} (u : Fin n → ℝ) (z : ℂ) :
    angleEvaluation u (constantL n z)=z := by
  change angleEvaluation u (monomialL 0 z)=_
  simp
@[simp] lemma angleEvaluation_variable {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    angleEvaluation u (monomialL (variableExponent i) 1)=anglePhase (u i) := by
  simp [variableExponent,Pi.single_apply]

lemma rationalAt_const_complex {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) (z : ℂ) :
    RationalAt φ.toRingHom (constF n z) z := by
  have hh:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField n) (constantL n z)
  rw [map_constantL] at hh
  have he : φ (constantL n z)=z := φ.commutes z
  simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,he] using hh

lemma rationalAt_angle_variable {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    RationalAt (angleEvaluation u).toRingHom (variableF i) (anglePhase (u i)) := by
  have hh:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n)
    (monomialL (variableExponent i) 1)
  change RationalAt (angleEvaluation u).toRingHom (variableF i)
    (angleEvaluation u (monomialL (variableExponent i) 1)) at hh
  simpa only [angleEvaluation_variable] using hh

lemma rationalAt_angle_sin {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) :
    RationalAt φ.toRingHom (torusSin x) (Real.sin u:ℂ) := by
  rw [←anglePhase_sine]
  exact (h.sub (h.inv (anglePhase_ne_zero _))).div
    ((RationalAt.natCast 2).mul (rationalAt_const_complex φ Complex.I))
    (mul_ne_zero (by norm_num) Complex.I_ne_zero)

lemma rationalAt_angle_cos {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) :
    RationalAt φ.toRingHom (torusCos x) (Real.cos u:ℂ) := by
  rw [←anglePhase_cosine]
  exact (h.add (h.inv (anglePhase_ne_zero _))).div (RationalAt.natCast 2) (by norm_num)

lemma rationalAt_angle_L {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) :
    RationalAt φ.toRingHom (torusL x) (L u:ℂ) := by
  have hq:=rationalAt_const_complex φ phase
  have hp (k : ℕ) : RationalAt φ.toRingHom (constF n phase^k*x) (anglePhase ((k:ℝ)*lambda+u)) := by
    simpa only [anglePhase_add,anglePhase_nat_mul,anglePhase_lambda] using (hq.pow k).mul h
  simpa only [torusL,L,Complex.ofReal_mul,Nat.cast_ofNat] using
    (rationalAt_angle_sin φ (hp 2)).mul (rationalAt_angle_sin φ (hp 3))

lemma rationalAt_angle_weights {n : ℕ} (φ : Laurent n →ₐ[ℂ] ℂ) {x : SpectralField n} {u : ℝ}
    (h : RationalAt φ.toRingHom x (anglePhase u)) (hL : L u≠0) (t : Tile) :
    RationalAt φ.toRingHom ((torusWeights x).tile t) ((physicalWeights u).tile t:ℂ) := by
  have hq:=rationalAt_const_complex φ phase
  have hd:=rationalAt_const_complex φ d
  have hs:=rationalAt_angle_sin φ h
  have hp (k : ℕ) : RationalAt φ.toRingHom (constF n phase^k/x) (anglePhase ((k:ℝ)*lambda-u)) := by
    simpa only [anglePhase_sub,anglePhase_nat_mul,anglePhase_lambda] using (hq.pow k).div h (anglePhase_ne_zero _)
  have ha: RationalAt φ.toRingHom (x/constF n phase) (anglePhase (u-lambda)) := by
    simpa only [anglePhase_sub,anglePhase_lambda] using h.div hq phase_ne_zero
  have ht:=rationalAt_angle_sin φ (hp 3)
  have hv:=rationalAt_angle_sin φ (hp 2)
  have hh:=rationalAt_angle_sin φ ha
  have hℓ:=rationalAt_angle_L φ h
  have hℓ₀ : (L u:ℂ)≠0 := by exact_mod_cast hL
  cases t
  · exact RationalAt.one
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hd.mul ht).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hd.mul ht).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hs.mul ht).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hs.mul ht).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hd.mul hs).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hd.mul hs).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (ht.mul hv).div hℓ hℓ₀
  · simpa [torusWeights,Weights.tile,physicalWeights,d] using (hh.mul hs).div hℓ hℓ₀

lemma rationalAt_angle_spectralA {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    RationalAt (angleEvaluation u).toRingHom (spectralA i) (Real.cos (2*u i-3*lambda):ℂ) := by
  apply rationalAt_angle_cos
  rw [anglePhase_sub,show anglePhase (2*u i)=anglePhase (u i)^2 from anglePhase_nat_mul 2 _,
    show anglePhase (3*lambda)=phase^3 from anglePhase_nat_mul 3 _]
  exact
    ((rationalAt_angle_variable u i).pow 2).div
      ((rationalAt_const_complex (angleEvaluation u) phase).pow 3) (pow_ne_zero _ phase_ne_zero)

lemma rationalAt_angle_spectralWeights {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (i : Fin n) (t : Tile) :
    RationalAt (angleEvaluation u).toRingHom ((spectralWeights n i).tile t)
      ((physicalWeights (3*lambda-u i)).tile t:ℂ) := by
  apply rationalAt_angle_weights _ _ (hL i)
  rw [anglePhase_sub,show anglePhase (3*lambda)=phase^3 from anglePhase_nat_mul 3 _]
  exact ((rationalAt_const_complex (angleEvaluation u) phase).pow 3).div
      (rationalAt_angle_variable u i) (anglePhase_ne_zero _)

lemma angleEvaluation_rowCosine {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    angleEvaluation u (rowCosineL i)=(Real.cos (2*u i-3*lambda):ℂ) := by
  have hh:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n) (rowCosineL i)
  rw [rowCosineL_algebraMap] at hh
  exact hh.unique (rationalAt_angle_spectralA u i)

lemma angleEvaluation_scalar {n : ℕ} (u : Fin n → ℝ) :
    angleEvaluation u (polynomialVacuumVector n (empty n))=
      scalarValue (RingHom.id ℂ) (fun i=>(Real.cos (2*u i-3*lambda):ℂ)) := by
  rw [←scalarValue_rowCosine]
  have hh:=map_scalarValue (angleEvaluation u).toRingHom (constantL n) rowCosineL
  have hc : (angleEvaluation u).toRingHom.comp (constantL n)=RingHom.id ℂ := by ext z; simp
  rw [hc] at hh
  have hf : (angleEvaluation u).toRingHom ∘ rowCosineL=fun i=>(Real.cos (2*u i-3*lambda):ℂ) := by
    funext i
    exact angleEvaluation_rowCosine u i
  rw [hf] at hh
  exact hh

lemma continuous_angleEvaluation {n : ℕ} (f : Laurent n) :
    Continuous (fun u : Fin n → ℝ=>angleEvaluation u f) := by
  induction f using AddMonoidAlgebra.induction_on with
  | of e =>
    change Continuous (fun u : Fin n → ℝ=>angleEvaluation u (monomialL e 1))
    simp only [angleEvaluation_monomial]
    apply continuous_const.mul
    apply continuous_finsetProd
    intro i _
    apply Continuous.zpow₀ _ _ (fun _=>Or.inl (anglePhase_ne_zero _))
    unfold anglePhase
    fun_prop
  | add f g hf hg =>
    simp only [map_add]
    exact hf.add hg
  | smul z f hf =>
    simp only [map_smul,smul_eq_mul]
    exact continuous_const.mul hf

end
end CriticalStrip.Diagram

 

 

 

namespace CriticalStrip.PositiveMatrix
noncomputable section
open Filter Matrix
open scoped BigOperators Topology Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Nonnegative (Q : Matrix ι ι ℝ) : Prop := ∀ i j, 0≤Q i j

def SummablePowers (Q : Matrix ι ι ℝ) : Prop := ∀ i j, Summable (fun k : ℕ => (Q^k) i j)

def Accessible (Q : Matrix ι ι ℝ) (v : ι → ℝ) : Prop :=
  ∀ i, ∃ k : ℕ, 0<(Q^k).mulVec v i

lemma Nonnegative.pow {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) (k : ℕ) :
    Nonnegative (Q^k) := by
  induction k with
  | zero => intro i j; simp only [pow_zero,Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ]
    exact Finset.sum_nonneg fun a _ =>mul_nonneg (ih i a) (hQ a j)

omit [DecidableEq ι] in
lemma Nonnegative.mulVec {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q)
    {z : ι → ℝ} (hz : ∀ i,0≤z i) : ∀ i, 0≤Q.mulVec z i :=
  fun _ =>Finset.sum_nonneg fun j _ =>mul_nonneg (hQ _ j) (hz j)

omit [DecidableEq ι] in
lemma Nonnegative.mulVec_mono {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q)
    {x y : ι → ℝ} (hxy : ∀ i,x i≤y i) : ∀ i, Q.mulVec x i≤Q.mulVec y i :=
  fun _ =>Finset.sum_le_sum fun j _ =>mul_le_mul_of_nonneg_left (hxy j) (hQ _ j)

omit [DecidableEq ι] in
lemma entry_mul_le_mulVec {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q)
    {z : ι → ℝ} (hz : ∀ i,0≤z i) (i j : ι) : Q i j*z j≤Q.mulVec z i :=
  Finset.single_le_sum (fun a _ =>mul_nonneg (hQ i a) (hz a)) (Finset.mem_univ j)

lemma stationary_partial_sum {Q : Matrix ι ι ℝ} {v w : ι → ℝ}
    (he : Q.mulVec w+v=w) (k : ℕ) :
    (∑ m∈Finset.range k, (Q^m).mulVec v)+(Q^k).mulVec w=w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,pow_succ,←Matrix.mulVec_mulVec,add_assoc,
      ←Matrix.mulVec_add,add_comm v (Q.mulVec w),he]
    exact ih

 
lemma summable_injection {Q : Matrix ι ι ℝ} {v w : ι → ℝ}
    (hQ : Nonnegative Q) (hv : ∀i,0≤v i) (hw : ∀i,0≤w i)
    (he : Q.mulVec w+v=w) (i : ι) : Summable (fun k : ℕ =>(Q^k).mulVec v i) := by
  apply summable_of_sum_range_le (fun k =>(hQ.pow k).mulVec hv i) (c:=w i)
  intro k
  have hh:=congrFun (stationary_partial_sum he k) i
  simp only [Pi.add_apply,Finset.sum_apply] at hh
  linarith [(hQ.pow k).mulVec hw i]

 

theorem summablePowers_of_stationary {Q : Matrix ι ι ℝ} {v w : ι → ℝ}
    (hQ : Nonnegative Q) (hv : ∀i,0≤v i) (hw : ∀i,0≤w i)
    (he : Q.mulVec w+v=w) (ha : Accessible Q v) : SummablePowers Q := by
  intro i j
  obtain ⟨m,hm⟩:=ha j
  have hs := (summable_nat_add_iff m).mpr (summable_injection hQ hv hw he i)
  apply (hs.div_const ((Q^m).mulVec v j)).of_nonneg_of_le (fun k =>hQ.pow k i j)
  intro k
  apply (le_div_iff₀ hm).mpr
  simpa only [pow_add,Matrix.mulVec_mulVec] using
    entry_mul_le_mulVec (hQ.pow k) ((hQ.pow m).mulVec hv) i j

lemma SummablePowers.tendsto_zero {Q : Matrix ι ι ℝ} (hs : SummablePowers Q) (i j : ι) :
    Tendsto (fun k : ℕ =>(Q^k) i j) atTop (𝓝 0) := (hs i j).tendsto_atTop_zero

lemma SummablePowers.mulVec_tendsto_zero {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (w : ι → ℝ) (i : ι) : Tendsto (fun k : ℕ =>(Q^k).mulVec w i) atTop (𝓝 0) := by
  simpa only [Matrix.mulVec,dotProduct,zero_mul,Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ =>(hs.tendsto_zero i j).mul_const (w j))

lemma SummablePowers.mulVec_summable {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (v : ι → ℝ) (i : ι) : Summable (fun k : ℕ =>(Q^k).mulVec v i) :=
  summable_sum fun j _ =>(hs i j).mul_right (v j)

 

lemma SummablePowers.stationary_eq_tsum {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    {v w : ι → ℝ} (he : Q.mulVec w+v=w) (i : ι) :
    w i=∑' k : ℕ,(Q^k).mulVec v i := by
  have hlim:=((hs.mulVec_summable v i).hasSum.tendsto_sum_nat).add (hs.mulVec_tendsto_zero w i)
  simp only [add_zero] at hlim
  have hc : Tendsto (fun k : ℕ =>(∑ m∈Finset.range k, (Q^m).mulVec v i)+(Q^k).mulVec w i)
      atTop (𝓝 (w i)) := by
    have hh : (fun k : ℕ =>(∑ m∈Finset.range k, (Q^m).mulVec v i)+(Q^k).mulVec w i)=fun _=>w i := by
      funext k
      simpa only [Pi.add_apply,Finset.sum_apply] using congrFun (stationary_partial_sum he k) i
    rw [hh]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hc hlim

lemma SummablePowers.stationary_nonneg {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (hQ : Nonnegative Q) {v w : ι → ℝ} (hv : ∀i,0≤v i) (he : Q.mulVec w+v=w) :
    ∀ i,0≤w i := by
  intro i
  rw [hs.stationary_eq_tsum he i]
  exact tsum_nonneg fun k =>(hQ.pow k).mulVec hv i

lemma SummablePowers.unique_stationary {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    {v w z : ι → ℝ} (he : Q.mulVec w+v=w) (hz : Q.mulVec z+v=z) : w=z := by
  funext i
  rw [hs.stationary_eq_tsum he i,hs.stationary_eq_tsum hz i]

 
lemma pow_mulVec_le {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) {z : ι → ℝ}
    {r : ℝ} (hr : 0≤r) (hz : ∀i,Q.mulVec z i≤r*z i) (k : ℕ) :
    ∀ i,(Q^k).mulVec z i≤r^k*z i := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro i
    rw [pow_succ',←Matrix.mulVec_mulVec,pow_succ']
    calc
      Q.mulVec ((Q^k).mulVec z) i≤Q.mulVec (fun j=>r^k*z j) i := hQ.mulVec_mono ih i
      _ = r^k*Q.mulVec z i := by
        simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ r^k*(r*z i) := mul_le_mul_of_nonneg_left (hz i) (pow_nonneg hr k)
      _ = _ := by ring

lemma summablePowers_of_le {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) {z : ι → ℝ}
    (hz : ∀i,0<z i) {r : ℝ} (hr : 0≤r) (hr₁ : r<1)
    (he : ∀i,Q.mulVec z i≤r*z i) : SummablePowers Q := by
  intro i j
  have hs:=((summable_geometric_of_lt_one hr hr₁).mul_left (z i)).div_const (z j)
  apply hs.of_nonneg_of_le (fun k=>hQ.pow k i j)
  intro k
  apply (le_div_iff₀ (hz j)).mpr
  exact (entry_mul_le_mulVec (hQ.pow k) (fun i=>(hz i).le) i j).trans
    (by simpa only [mul_comm] using pow_mulVec_le hQ hr he k i)

def HasSupervector (Q : Matrix ι ι ℝ) : Prop :=
  ∃ z : ι → ℝ, (∀i,0<z i) ∧ ∀i,Q.mulVec z i<z i

lemma HasSupervector.summablePowers {Q : Matrix ι ι ℝ} (h : HasSupervector Q)
    (hQ : Nonnegative Q) : SummablePowers Q := by
  obtain ⟨z,hz,he⟩:=h
  classical
  cases isEmpty_or_nonempty ι with
  | inl hi => intro i; exact isEmptyElim i
  | inr hi =>
    let r := Finset.univ.sup' Finset.univ_nonempty (fun i=>Q.mulVec z i/z i)
    have hr₁ : r<1 := (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ =>(div_lt_one (hz i)).mpr (he i))
    have hr₀ : 0≤r := by
      obtain ⟨i⟩:=hi
      exact (div_nonneg (hQ.mulVec (fun i=>(hz i).le) i) (hz i).le).trans
        (Finset.le_sup' (fun i=>Q.mulVec z i/z i) (Finset.mem_univ i))
    apply summablePowers_of_le hQ hz hr₀ hr₁
    intro i
    exact (div_le_iff₀ (hz i)).mp (Finset.le_sup' (fun i=>Q.mulVec z i/z i) (Finset.mem_univ i))

lemma SummablePowers.hasSupervector {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (hQ : Nonnegative Q) : HasSupervector Q := by
  let z : ι → ℝ:=fun i=>∑' k : ℕ,(Q^k).mulVec (fun _=>1) i
  have hz : ∀i,1≤z i := by
    intro i
    have hh:=Summable.le_tsum (hs.mulVec_summable (fun _=>1) i) 0
      (fun k _ =>(hQ.pow k).mulVec (fun _=>by norm_num) i)
    simpa only [pow_zero,Matrix.one_mulVec] using hh
  have he : ∀ i,Q.mulVec z i+1=z i := by
    intro i
    have hh := (hs.mulVec_summable (fun _=>1) i).tsum_eq_zero_add
    simp only [pow_zero,Matrix.one_mulVec] at hh
    suffices hQz : Q.mulVec z i=∑' k : ℕ,(Q^(k+1)).mulVec (fun _=>1) i by
      rw [hQz]; linarith
    change (∑ j, Q i j * ∑' k : ℕ,(Q^k).mulVec (fun _=>1) j) = _
    simp_rw [← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun j _ =>(hs.mulVec_summable (fun _=>1) j).mul_left (Q i j))]
    congr 1
    funext k
    change Q.mulVec ((Q^k).mulVec (fun _=>1)) i=(Q^(k+1)).mulVec (fun _=>1) i
    rw [Matrix.mulVec_mulVec,pow_succ']
  refine ⟨z,fun i=>lt_of_lt_of_le (by norm_num) (hz i),?_⟩
  intro i
  linarith [he i]

lemma hasSupervector_iff {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) :
    HasSupervector Q ↔ SummablePowers Q := ⟨fun h=>h.summablePowers hQ,fun hs=>hs.hasSupervector hQ⟩

omit [DecidableEq ι] in
lemma isOpen_hasSupervector : IsOpen {Q : Matrix ι ι ℝ | HasSupervector Q} := by
  have he : {Q : Matrix ι ι ℝ | HasSupervector Q}=
      ⋃ z : ι → ℝ, ⋃ (_ : ∀i,0<z i), ⋂ i : ι, {Q : Matrix ι ι ℝ | Q.mulVec z i<z i} := by
    ext Q
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_iInter,HasSupervector,exists_prop]
  rw [he]
  apply isOpen_iUnion
  intro z
  apply isOpen_iUnion
  intro _
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (by unfold Matrix.mulVec dotProduct; fun_prop) continuous_const

 

theorem summablePowers_of_connected_stationary
    {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    (Q : α → Matrix ι ι ℝ) (v w : α → ι → ℝ) (a : α)
    (hQc : Continuous Q) (hwc : Continuous w)
    (hQ : ∀ t, Nonnegative (Q t)) (hv : ∀ t i, 0≤v t i)
    (he : ∀ t,(Q t).mulVec (w t)+v t=w t)
    (hs : SummablePowers (Q a)) (ha : ∀ t,t≠a → Accessible (Q t) (v t)) :
    ∀ t,SummablePowers (Q t) := by
  let S : Set α := {t | SummablePowers (Q t)}
  have hS : S={t | ∀ i,0≤w t i} := by
    ext t
    constructor
    · intro ht
      exact ht.stationary_nonneg (hQ t) (hv t) (he t)
    · intro ht
      by_cases ht' : t=a
      · simpa only [S,Set.mem_ofPred_eq,ht'] using hs
      · exact summablePowers_of_stationary (hQ t) (hv t) ht (he t) (ha t ht')
  have hc : IsClosed S := by
    rw [hS,show {t | ∀ i,0≤w t i}=⋂ i, {t | 0≤w t i} by ext; simp]
    exact isClosed_iInter fun i =>isClosed_le continuous_const ((continuous_apply i).comp hwc)
  have ho : IsOpen S := by
    have hh : S=Q ⁻¹' {M | HasSupervector M} := by
      ext t
      exact (hasSupervector_iff (hQ t)).symm
    rw [hh]
    exact isOpen_hasSupervector.preimage hQc
  have hu : S=Set.univ := (show IsClopen S from ⟨hc,ho⟩).eq_univ ⟨a,hs⟩
  intro t
  show t∈S
  rw [hu]
  trivial

 
theorem summablePowers_on_Icc
    (Q : ℝ → Matrix ι ι ℝ) (v w : ℝ → ι → ℝ) {a b : ℝ} (hab : a≤b)
    (hQc : ContinuousOn Q (Set.Icc a b)) (hwc : ContinuousOn w (Set.Icc a b))
    (hQ : ∀t∈Set.Icc a b,Nonnegative (Q t))
    (hv : ∀t∈Set.Icc a b,∀i,0≤v t i)
    (he : ∀t∈Set.Icc a b,(Q t).mulVec (w t)+v t=w t)
    (hs : SummablePowers (Q a))
    (ha : ∀t∈Set.Ioc a b,Accessible (Q t) (v t)) :
    ∀t∈Set.Icc a b,SummablePowers (Q t) := by
  let : PreconnectedSpace (Set.Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hh:=summablePowers_of_connected_stationary
    (fun t : Set.Icc a b=>Q t.val) (fun t : Set.Icc a b=>v t.val)
    (fun t : Set.Icc a b=>w t.val) ⟨a,le_rfl,hab⟩
    hQc.domRestrict hwc.domRestrict (fun t=>hQ _ t.property) (fun t=>hv _ t.property)
    (fun t=>he _ t.property) hs (fun t ht=>ha _ ⟨lt_of_le_of_ne t.property.1
      (by intro hr; exact ht (Subtype.ext hr.symm)),t.property.2⟩)
  exact fun t ht=>hh ⟨t,ht⟩

 

theorem SummablePowers.weighted {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (hQ : Nonnegative Q) (d : ℕ) (i j : ι) :
    Summable (fun k : ℕ=>(k:ℝ)^d*(Q^k) i j) := by
  obtain ⟨z,hz,he⟩:=hs.hasSupervector hQ
  let r := Finset.univ.sup' ⟨i,Finset.mem_univ i⟩ (fun i=>Q.mulVec z i/z i)
  have hr₁ : r<1 := (Finset.sup'_lt_iff _).mpr (fun i _=>(div_lt_one (hz i)).mpr (he i))
  have hr₀ : 0≤r := (div_nonneg (hQ.mulVec (fun i=>(hz i).le) i) (hz i).le).trans
    (Finset.le_sup' (fun i=>Q.mulVec z i/z i) (Finset.mem_univ i))
  have hle : ∀i,Q.mulVec z i≤r*z i := fun i=>(div_le_iff₀ (hz i)).mp
    (Finset.le_sup' (fun i=>Q.mulVec z i/z i) (Finset.mem_univ i))
  have hg : Summable (fun k : ℕ=>(k:ℝ)^d*r^k) :=
    summable_pow_mul_geometric_of_norm_lt_one d (by simpa [Real.norm_eq_abs,abs_of_nonneg hr₀] using hr₁)
  apply ((hg.mul_right (z i)).div_const (z j)).of_nonneg_of_le
    (fun k=>mul_nonneg (by positivity) (hQ.pow k i j))
  intro k
  have hk : (Q^k) i j≤r^k*z i/z j := (le_div_iff₀ (hz j)).mpr
    ((entry_mul_le_mulVec (hQ.pow k) (fun i=>(hz i).le) i j).trans (pow_mulVec_le hQ hr₀ hle k i))
  simpa only [mul_div_assoc,mul_assoc] using mul_le_mul_of_nonneg_left hk (show 0≤(k:ℝ)^d by positivity)

end
end CriticalStrip.PositiveMatrix

end OAI
