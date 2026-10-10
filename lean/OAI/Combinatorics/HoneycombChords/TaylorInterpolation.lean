import OAI.Combinatorics.HoneycombChords.TranslatedJets

namespace OAI

/-! Translated Taylor minors and physical interpolation residual bounds.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset

lemma polynomialJet_X_pow_above {k j : ℕ} (h : k < j) (x : ℝ) :
    polynomialJet ((X:Polynomial ℝ)^k) x j=0 := by
  simp [polynomialJet_X_pow,Nat.choose_eq_zero_of_lt h]

lemma polynomialJet_X_pow_sum (k : ℕ) (x y : ℝ) :
    ∑ j∈range (k+1),polynomialJet ((X:Polynomial ℝ)^k) x j*y^j=(x+y)^k := by
  have h := (taylor x ((X:Polynomial ℝ)^k)).eval_eq_sum_range y
  rw [natDegree_taylor,natDegree_X_pow] at h
  simpa only [polynomialJet,taylor_eval,eval_pow,eval_X,add_comm] using h.symm

noncomputable def kernelTaylorTerm (r : ℕ) (b x y : ℝ) (k j : ℕ) : ℝ :=
  kernelJetTerm r j b x k*y^j

lemma kernelTaylorTerm_above (r : ℕ) (b x y : ℝ) {k j : ℕ} (h : k < j) :
    kernelTaylorTerm r b x y k j=0 := by
  simp only [kernelTaylorTerm,kernelJetTerm,polynomialJet_X_pow_above h,mul_zero,zero_div,zero_mul]

lemma kernelTaylorTerm_bound (r k j : ℕ) {b x y B X Y : ℝ}
    (hB : 1 ≤ B) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hb : |b| ≤ B) (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    ‖kernelTaylorTerm r b x y k j‖ ≤ (4*B*X*Y)^k/(2*k).factorial := by
  by_cases hj : j ≤ k
  · rw [kernelTaylorTerm,norm_mul,norm_pow,Real.norm_eq_abs y]
    calc
      ‖kernelJetTerm r j b x k‖*|y|^j ≤ ((4*B*X)^k/(2*k).factorial)*Y^k :=
        mul_le_mul (kernelJetTerm_bound r j k hB hX hb hx)
          ((pow_le_pow_left₀ (abs_nonneg _) hy j).trans (pow_le_pow_right₀ hY hj))
          (by positivity) (by positivity)
      _=(4*B*X*Y)^k/(2*k).factorial := by rw [mul_pow];ring
  · rw [kernelTaylorTerm_above r b x y (lt_of_not_ge hj),norm_zero]
    positivity

lemma kernelTaylorTerm_norm_row_bound (r k : ℕ) {b x y B X Y : ℝ}
    (hB : 1 ≤ B) (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hb : |b| ≤ B) (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    ∑' j,‖kernelTaylorTerm r b x y k j‖ ≤ (8*B*X*Y)^k/(2*k).factorial := by
  rw [tsum_eq_sum (s:=range (k+1)) (fun j hj => by
    rw [kernelTaylorTerm_above r b x y (by simp only [mem_range,not_lt] at hj;omega),norm_zero])]
  have hn : ((k+1:ℕ):ℝ) ≤ (2:ℝ)^k := by exact_mod_cast Nat.succ_le_of_lt k.lt_two_pow_self
  calc
    ∑ j∈range (k+1),‖kernelTaylorTerm r b x y k j‖ ≤
        ∑ j∈range (k+1),(4*B*X*Y)^k/(2*k).factorial := sum_le_sum (fun j _ => kernelTaylorTerm_bound r k j hB hX hY hb hx hy)
    _=((k+1:ℕ):ℝ)*((4*B*X*Y)^k/(2*k).factorial) := by simp
    _ ≤ (2:ℝ)^k*((4*B*X*Y)^k/(2*k).factorial) := mul_le_mul_of_nonneg_right hn (by positivity)
    _=(8*B*X*Y)^k/(2*k).factorial := by rw [←mul_div_assoc,←mul_pow];ring_nf

lemma kernelTaylorTerm_summable (r : ℕ) (b x y : ℝ) :
    Summable (Function.uncurry (kernelTaylorTerm r b x y)) := by
  have hn : Summable (fun p : ℕ×ℕ => ‖kernelTaylorTerm r b x y p.1 p.2‖) := by
    apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
    constructor
    · intro k
      apply summable_of_ne_finset_zero (s:=range (k+1))
      intro j hj
      rw [kernelTaylorTerm_above r b x y (by simp only [mem_range,not_lt] at hj;omega),norm_zero]
    · exact (summable_evenFactorial (show 0 ≤ 8*(|b|+1)*(|x|+1)*(|y|+1) by positivity)).of_nonneg_of_le
        (fun k => tsum_nonneg (fun j => norm_nonneg _))
        (fun k => kernelTaylorTerm_norm_row_bound r k (by linarith [abs_nonneg b])
          (by linarith [abs_nonneg x]) (by linarith [abs_nonneg y]) (by linarith) (by linarith) (by linarith))
  exact hn.of_norm

lemma kernelTaylorTerm_row_sum (r k : ℕ) (b x y : ℝ) :
    ∑' j,kernelTaylorTerm r b x y k j=kernelJetTerm r 0 b (x+y) k := by
  rw [tsum_eq_sum (s:=range (k+1)) (fun j hj => kernelTaylorTerm_above r b x y (by simp only [mem_range,not_lt] at hj;omega))]
  simp only [kernelTaylorTerm,kernelJetTerm,polynomialJet_zero,eval_pow,eval_X]
  have hm : (∑ j∈range (k+1),polynomialJet (X^k) b r*polynomialJet (X^k) x j/(2*k).factorial*y^j)=
      polynomialJet (X^k) b r/(2*k).factorial*(∑ j∈range (k+1),polynomialJet (X^k) x j*y^j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  rw [hm,polynomialJet_X_pow_sum]
  ring

lemma cosineKernelJet_translation_summable (r : ℕ) (b x y : ℝ) :
    Summable (fun j => cosineKernelJet r j b x*y^j) := by
  have h := (kernelTaylorTerm_summable r b x y).prod_symm.prod
  simpa only [Function.uncurry,kernelTaylorTerm,Prod.swap_prod_mk,tsum_mul_right,cosineKernelJet] using h

lemma cosineKernelJet_translation (r : ℕ) (b x y : ℝ) :
    cosineKernelJet r 0 b (x+y)=∑' j,cosineKernelJet r j b x*y^j := by
  have h := (kernelTaylorTerm_summable r b x y).tsum_comm
  calc
    cosineKernelJet r 0 b (x+y)=∑' k,∑' j,kernelTaylorTerm r b x y k j := by
      simp only [kernelTaylorTerm_row_sum,cosineKernelJet]
    _=∑' j,∑' k,kernelTaylorTerm r b x y k j := h.symm
    _=∑' j,cosineKernelJet r j b x*y^j := by
      simp only [kernelTaylorTerm,tsum_mul_right,cosineKernelJet]

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix

lemma cosineKernelJet_at_zero_all (r j : ℕ) (x : ℝ) :
    cosineKernelJet r j 0 x=polynomialJet (X^r) x j/(2*r).factorial := by
  unfold cosineKernelJet kernelJetTerm
  simp only [polynomialJet_at_zero_X_pow]
  rw [tsum_eq_single r]
  · simp
  · intro k hk
    simp [hk]

lemma nodalOrder_initial_zero {b : ℕ → ℝ} {i : ℕ}
    (hb : ∀ j,j ≤ i → b j=0) : nodalOrder b i=i := by
  unfold nodalOrder
  have he : (range i).filter (fun j=>b j=b i)=range i := by
    apply filter_eq_self.mpr
    intro j hj
    rw [hb j (Nat.le_of_lt (mem_range.mp hj)),hb i le_rfl]
  rw [he,card_range]

lemma polynomialJet_sum_coeff (P : Polynomial ℝ) {n : ℕ} (hn : P.natDegree < n) (x : ℝ) (j : ℕ) :
    polynomialJet P x j=∑ i : Fin n,P.coeff i*polynomialJet (X^i.val) x j := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow' hn]
  simp only [polynomialJet,map_sum,finsetSum_coeff]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ=>P.coeff i*((taylor x) (X^i)).coeff j) n]
  apply sum_congr rfl
  intro i hi
  simp [taylor_mul,taylor_C]

lemma polynomialJet_shifted_power (a : ℝ) (k j : ℕ) :
    polynomialJet ((X+Polynomial.C a)^k) (-a) j=if k=j then 1 else 0 := by
  simp [polynomialJet,map_add,taylor_X,taylor_C,coeff_X_pow,eq_comm]


lemma kernel_coeff_det_zero_missing {n q : ℕ} (b : ℕ → ℝ) (a : ℝ)
    (hq : q < n) (hb : ∀ i,i ≤ q → b i=0) (e : Fin n → ℕ)
    (hmiss : ∃ k,k ≤ q ∧ ∀ i,e i≠k) :
    Matrix.det (fun i j : Fin n=>cosineKernelJet (nodalOrder b j) (e i) (b j) (-a))=0 := by
  classical
  obtain ⟨k,hk,hmiss⟩ := hmiss
  let P : Polynomial ℝ := (X+Polynomial.C a)^k
  have hdeg : P.natDegree=k := by simp [P,natDegree_pow]
  let v : Fin n → ℝ := fun i=>((2*i.val).factorial:ℝ)*P.coeff i
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j=>cosineKernelJet (nodalOrder b j) (e i) (b j) (-a)
  have he (i j : Fin n) : A i j*v j=P.coeff j*polynomialJet (X^j.val) (-a) (e i) := by
    by_cases hj : j.val ≤ q
    · have hb' : b j=0 := hb j hj
      have hn : nodalOrder b j=j.val := nodalOrder_initial_zero (fun l hl=>hb l (hl.trans hj))
      dsimp [A,v]
      rw [hb',hn,cosineKernelJet_at_zero_all]
      field_simp
    · have hz : P.coeff j=0 := coeff_eq_zero_of_natDegree_lt (by rw [hdeg];omega)
      simp [v,hz]
  have hav : A*ᵥ v=0 := by
    ext i
    simp only [Matrix.mulVec,dotProduct,Pi.zero_apply]
    simp_rw [he]
    rw [←polynomialJet_sum_coeff P (by rw [hdeg];omega)]
    simp [P,polynomialJet_shifted_power,Ne.symm (hmiss i)]
  have hv : v≠0 := by
    intro h
    have hi := congrFun h (⟨k,by omega⟩ : Fin n)
    have hc : P.coeff k=1 := by simp [P,coeff_X_add_C_pow]
    have hn : (2*k).factorial ≠ 0 := Nat.factorial_ne_zero _
    simp [v,hc,hn] at hi
  by_contra hd
  have hu : Function.Injective (A.mulVec) := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hd))
  exact hv (hu (by rw [hav,Matrix.mulVec_zero]))

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset Filter Topology

noncomputable def translatedKernelMatrix {n : ℕ} (b : ℕ → ℝ) (a : ℝ) (v : ℕ → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j=>cosineKernelJet (nodalOrder b i) 0 (b i) (-a+v j)
noncomputable def kernelComplementMatrix {n : ℕ} (b : ℕ → ℝ) (a : ℝ) (v : ℕ → ℝ)
    (g : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j=>
    cosineKernelJet (nodalOrder b i) 0 (b i) (-a+v j)+
      cosineKernelJet (nodalOrder b i) 0 (b i) (-a)*(g (v j)-1)
noncomputable def kernelOriginFunctional {n : ℕ} (b : ℕ → ℝ) (a : ℝ) (v : ℕ → ℝ)
    (g : ℝ → ℝ) : ℝ :=
    (kernelComplementMatrix (n:=n) b a v g).det/(translatedKernelMatrix (n:=n) b a v).det

lemma kernel_origin_modified_hasSum {n : ℕ} (r : ℕ) (b a : ℝ) (v : ℕ → ℝ)
    (g : ℝ → ℝ) (j : Fin (n+1)) :
    HasSum (fun k=>cosineKernelJet r k b (-a)*originPowerData v g k j)
      (cosineKernelJet r 0 b (-a+v j)+cosineKernelJet r 0 b (-a)*(g (v j)-1)) := by
  have hk : HasSum (fun k=>cosineKernelJet r k b (-a)*(v j)^k)
      (cosineKernelJet r 0 b (-a+v j)) := by
    rw [cosineKernelJet_translation]
    exact (cosineKernelJet_translation_summable r b (-a) (v j)).hasSum
  have hs : HasSum (fun k : ℕ=>if k=0 then cosineKernelJet r 0 b (-a)*(g (v j)-1) else 0)
      (cosineKernelJet r 0 b (-a)*(g (v j)-1)) := hasSum_ite_eq 0 _
  convert hk.add hs using 1
  funext k
  by_cases h:k=0
  · subst k
    simp only [originPowerData,ite_true,pow_zero,mul_one]
    ring
  · simp [originPowerData,h]

/-- Infinite Cauchy--Binet bound for the exact translated kernel. The only
input on g is the previously proved sparse polynomial-functional inequality. -/
lemma kernel_origin_det_bounds {n q : ℕ} {a R : ℝ}
    (ha : 0 ≤ a) (hR : 0 < R) (hphase : Real.sqrt R*Real.sqrt a < Real.pi/2)
    (b v : ℕ → ℝ) (g : ℝ → ℝ)
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hball : ∀ i,0 ≤ b i ∧ b i ≤ R)
    (hq : q ≤ n) (hbzero : ∀ i,i ≤ q → b i=0)
    (hv : ∀ i : Fin (n+1),0 < v i) (hord : StrictMono (fun i : Fin (n+1)=>v i))
    {L U : ℝ}
    (hbound : ∀ e : Fin n → ℕ,StrictMono e →
      (∀ k,1 ≤ k → k ≤ q → ∃ i,e i+1=k) → L ≤ sparseEval v e g ∧ sparseEval v e g ≤ U) :
    L*(translatedKernelMatrix (n:=n+1) b a v).det ≤ (kernelComplementMatrix (n:=n+1) b a v g).det ∧
      (kernelComplementMatrix (n:=n+1) b a v g).det ≤ U*(translatedKernelMatrix (n:=n+1) b a v).det := by
  let C : Fin (n+1) → ℕ → ℝ := fun i k=>cosineKernelJet (nodalOrder b i) k (b i) (-a)
  let A (m : ℕ) : Matrix (Fin (n+1)) (Fin m) ℝ := fun i k=>C i k
  let B (m : ℕ) : Matrix (Fin m) (Fin (n+1)) ℝ := fun k j=>(v j)^k.val
  let D (m : ℕ) : Matrix (Fin m) (Fin (n+1)) ℝ := fun k j=>originPowerData v g k j
  have hfin (m : ℕ) : L*(A m*B m).det ≤ (A m*D m).det ∧ (A m*D m).det ≤ U*(A m*B m).det := by
    apply positive_mixture_finite_bounds C v g hv hord
    · intro d hd
      exact translated_beta_jet_det_nonneg ha hR hphase b hb hball d hd
    · intro d hd hm
      exact kernel_coeff_det_zero_missing b a (by omega) hbzero d hm
    · exact hbound
  have htB : Tendsto (fun m=>A m*B m) atTop (𝓝 (translatedKernelMatrix (n:=n+1) b a v)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := (cosineKernelJet_translation_summable (nodalOrder b i) (b i) (-a) (v j)).hasSum.tendsto_sum_nat
    rw [←cosineKernelJet_translation] at h
    convert h using 1
    · funext m
      change (∑ k : Fin m,cosineKernelJet (nodalOrder b i) k (b i) (-a)*(v j)^k.val)=_
      exact Fin.sum_univ_eq_sum_range (fun k=>cosineKernelJet (nodalOrder b i) k (b i) (-a)*(v j)^k) m
    · rfl
  have htD : Tendsto (fun m=>A m*D m) atTop (𝓝 (kernelComplementMatrix (n:=n+1) b a v g)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := (kernel_origin_modified_hasSum (nodalOrder b i) (b i) a v g j).tendsto_sum_nat
    convert h using 1
    · funext m
      change (∑ k : Fin m,cosineKernelJet (nodalOrder b i) k (b i) (-a)*originPowerData v g k j)=_
      exact Fin.sum_univ_eq_sum_range (fun k=>cosineKernelJet (nodalOrder b i) k (b i) (-a)*originPowerData v g k j) m
    · rfl
  have hdet : Continuous (Matrix.det : Matrix (Fin (n+1)) (Fin (n+1)) ℝ → ℝ) := continuous_id.matrix_det
  have hB := hdet.continuousAt.tendsto.comp htB
  have hD := hdet.continuousAt.tendsto.comp htD
  exact ⟨le_of_tendsto_of_tendsto (hB.const_mul L) hD (Eventually.of_forall (fun m=>(hfin m).1)),
    le_of_tendsto_of_tendsto hD (hB.const_mul U) (Eventually.of_forall (fun m=>(hfin m).2))⟩

lemma translatedKernelMatrix_det_pos {n : ℕ} (b v : ℕ → ℝ) (a : ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hb0 : ∀ i : Fin n,0 ≤ b i)
    (hv : ∀ i : Fin n,a ≤ v i) (hord : StrictMono (fun i : Fin n=>v i)) :
    0 < (translatedKernelMatrix (n:=n) b a v).det := by
  apply jetEvaluation_det_pos b (fun i : Fin n=>-a+v i) hb
  · intro i j hij
    linarith [hord hij]
  · exact hb0
  · intro i
    linarith [hv i]

lemma kernel_origin_bounds {n q : ℕ} {a R : ℝ}
    (ha : 0 ≤ a) (hR : 0 < R) (hphase : Real.sqrt R*Real.sqrt a < Real.pi/2)
    (b v : ℕ → ℝ) (g : ℝ → ℝ)
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hball : ∀ i,0 ≤ b i ∧ b i ≤ R)
    (hq : q ≤ n) (hbzero : ∀ i,i ≤ q → b i=0)
    (hv : ∀ i : Fin (n+1),0 < v i) (hx : ∀ i : Fin (n+1),a ≤ v i)
    (hord : StrictMono (fun i : Fin (n+1)=>v i)) {L U : ℝ}
    (hbound : ∀ e : Fin n → ℕ,StrictMono e →
      (∀ k,1 ≤ k → k ≤ q → ∃ i,e i+1=k) → L ≤ sparseEval v e g ∧ sparseEval v e g ≤ U) :
    L ≤ kernelOriginFunctional (n:=n+1) b a v g ∧ kernelOriginFunctional (n:=n+1) b a v g ≤ U := by
  have hd := translatedKernelMatrix_det_pos b v a hb (fun i=>(hball i).1) hx hord
  have h := kernel_origin_det_bounds ha hR hphase b v g hb hball hq hbzero hv hord hbound
  exact ⟨(le_div_iff₀ hd).mpr h.1,(div_le_iff₀ hd).mpr h.2⟩

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset

noncomputable def zeroShiftProduct (u : ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  (shiftedPole u 0)/(shiftedPole u 0+y)*
    (ReciprocalExpr.normalizedPole (shiftedPole u 2)).eval y*(physicalPairTail u m).eval y
noncomputable def oneShiftProduct (u : ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  (physicalTripleExpr u 0).eval y*(physicalTripleTail u m).eval y

lemma normalizedFast_tail_poles (u : ℝ) {A : ReciprocalExpr} (hA : A.PolesAbove (shiftedPole u 0)) :
    (ReciprocalExpr.mulExpr (ReciprocalExpr.normalizedPole (shiftedPole u 2)) A).PolesAbove (shiftedPole u 0) :=
  ReciprocalExpr.mulExpr_poles (ReciprocalExpr.normalizedPole_poles (shiftedPole_strictMono u (by omega))) hA
lemma normalizedFast_tail_coeff {u : ℝ} (hu4 : u ≤ 4) {A : ReciprocalExpr} (hA : A.CoeffNonneg) :
    (ReciprocalExpr.mulExpr (ReciprocalExpr.normalizedPole (shiftedPole u 2)) A).CoeffNonneg :=
  ReciprocalExpr.mulExpr_coeff (ReciprocalExpr.normalizedPole_coeff (shiftedPole_pos hu4 _).le) hA
lemma normalizedFast_tail_zero {u : ℝ} (hu4 : u ≤ 4) {A : ReciprocalExpr} (hA : A.eval 0=1) :
    (ReciprocalExpr.mulExpr (ReciprocalExpr.normalizedPole (shiftedPole u 2)) A).eval 0=1 := by
  rw [ReciprocalExpr.mulExpr_eval,ReciprocalExpr.normalizedPole_zero (shiftedPole_pos hu4 _),hA,mul_one]

lemma sparse_zero_shift_bounds {n q : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (v : ℕ → ℝ) (e : Fin n → ℕ)
    (hv : ∀ i,0 < v i) (hord : StrictMono (fun i : Fin (n+1)=>v i)) (he : StrictMono e)
    (hq : ∀ k,1 ≤ k → k ≤ q → ∃ i,e i+1=k) (m : ℕ) :
    poleProduct v (shiftedPole u 0) (n+1) ≤ sparseEval v e (fun y=>1-zeroShiftProduct u m y) ∧
    sparseEval v e (fun y=>1-zeroShiftProduct u m y) ≤ 2*poleProduct v (shiftedPole u 0) (q+1) := by
  let A:=ReciprocalExpr.mulExpr (ReciprocalExpr.normalizedPole (shiftedPole u 2)) (physicalPairTail u m)
  have hA:=normalizedFast_tail_poles u (physicalPairTail_poles u m)
  have hAp:=normalizedFast_tail_coeff hu4 (physicalPairTail_coeff hu4 m)
  have hAz:=normalizedFast_tail_zero hu4 (physicalPairTail_zero hu4 m)
  have hAC : A.eval (-shiftedPole u 0) ≤ 2 := by
    rw [ReciprocalExpr.mulExpr_eval,slowPole_eval]
    exact physicalPairTail_uniform hu hu4 m
  have hfunc : (fun y=>1-zeroShiftProduct u m y)=(fun y=>1-(shiftedPole u 0)/(shiftedPole u 0+y)*A.eval y) := by
    funext y
    simp only [zeroShiftProduct,A,ReciprocalExpr.mulExpr_eval]
    ring
  rw [hfunc]
  exact ⟨sparse_product_lower v e hv hord he (shiftedPole_pos hu4 0)
      (ReciprocalExpr.poles_mono (shiftedPole_pos hu4 0).le hA) hAp hAz,
    (sparse_product_upper v e hv hord he hq (shiftedPole_pos hu4 0) hA hAp hAz).trans
      (mul_le_mul_of_nonneg_right hAC (poleProduct_pos v hv (shiftedPole_pos hu4 0) _).le)⟩

lemma sparse_one_shift_bounds {n q : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (v : ℕ → ℝ) (e : Fin n → ℕ)
    (hv : ∀ i,0 < v i) (hord : StrictMono (fun i : Fin (n+1)=>v i)) (he : StrictMono e)
    (hq : ∀ k,1 ≤ k → k ≤ q → ∃ i,e i+1=k) (m : ℕ) :
    (1/2:ℝ)*poleProduct v (shiftedPole u 0) (n+1) ≤ sparseEval v e (fun y=>1-oneShiftProduct u m y) ∧
    sparseEval v e (fun y=>1-oneShiftProduct u m y) ≤ 2*poleProduct v (shiftedPole u 0) (q+1) := by
  let A:=physicalTripleTail u m
  let B:=ReciprocalExpr.mulExpr (ReciprocalExpr.normalizedPole (shiftedPole u 2)) A
  let p:=ReciprocalExpr.tripleWeight (shiftedPole u 0) (shiftedPole u 1) (shiftedPole u 2)
  have hp:=ReciprocalExpr.tripleWeight_pos (shiftedPole_pos hu4 0)
    (shiftedPole_strictMono u (by omega : 0<1)) (shiftedPole_strictMono u (by omega : 1<2))
  have hp1:=ReciprocalExpr.tripleWeight_lt_one (shiftedPole_pos hu4 0)
    (shiftedPole_strictMono u (by omega : 0<1)) (shiftedPole_strictMono u (by omega : 1<2))
  have hA:=physicalTripleTail_poles u m
  have hAp:=physicalTripleTail_coeff hu4 m
  have hAz:=physicalTripleTail_zero hu4 m
  have hBC : B.eval (-shiftedPole u 0) ≤ 2 := by
    rw [ReciprocalExpr.mulExpr_eval,slowPole_eval]
    exact physicalTripleTail_uniform hu hu4 m
  have hAC : A.eval (-shiftedPole u 0) ≤ 2 := by
    apply le_trans _ hBC
    rw [ReciprocalExpr.mulExpr_eval,slowPole_eval]
    exact le_mul_of_one_le_left (ReciprocalExpr.eval_nonneg hA hAp le_rfl)
      (poleTailRatio_ge_one hu4 (by omega))
  have h:=sparse_mixture_bounds v e hv hord he hq (shiftedPole_pos hu4 0) hp.le hp1.le
    hA hAp hAz (normalizedFast_tail_poles u hA) (normalizedFast_tail_coeff hu4 hAp)
    (normalizedFast_tail_zero hu4 hAz) hAC hBC
  have hfunc : (fun y=>1-oneShiftProduct u m y)=
      (fun y=>1-(p*((shiftedPole u 0)/(shiftedPole u 0+y)*A.eval y)+(1-p)*B.eval y)) := by
    funext y
    simp only [oneShiftProduct,physicalTripleExpr,Nat.mul_zero,Nat.zero_add,
      ReciprocalExpr.tripleFactor,ReciprocalExpr.eval,ReciprocalExpr.normalizedPole_eval,
      B,ReciprocalExpr.mulExpr_eval]
    change 1-(p*((shiftedPole u 0)/(shiftedPole u 0+y))+(1-p)*((shiftedPole u 2)/(shiftedPole u 2+y)))*A.eval y=_
    ring
  rw [hfunc]
  exact ⟨(mul_le_mul_of_nonneg_right (physical_first_weight_half hu hu4)
      (poleProduct_pos v hv (shiftedPole_pos hu4 0) _).le).trans h.1,h.2⟩

lemma kernel_zero_shift_bounds {n q : ℕ} {u R : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hR : 0 < R) (hphase : Real.sqrt R*Real.sqrt u < Real.pi/2)
    (b v : ℕ → ℝ) (hb : Monotone (fun i : Fin (n+1)=>b i)) (hball : ∀ i,0 ≤ b i ∧ b i ≤ R)
    (hq : q ≤ n) (hbzero : ∀ i,i ≤ q → b i=0) (hv : ∀ i,0 < v i)
    (hx : ∀ i : Fin (n+1),u ≤ v i) (hord : StrictMono (fun i : Fin (n+1)=>v i)) (m : ℕ) :
    poleProduct v (shiftedPole u 0) (n+1) ≤ kernelOriginFunctional (n:=n+1) b u v (fun y=>1-zeroShiftProduct u m y) ∧
    kernelOriginFunctional (n:=n+1) b u v (fun y=>1-zeroShiftProduct u m y) ≤ 2*poleProduct v (shiftedPole u 0) (q+1) := by
  apply kernel_origin_bounds hu hR hphase b v _ hb hball hq hbzero (fun i=>hv i) hx hord
  intro e he heq
  exact sparse_zero_shift_bounds hu hu4 v e hv hord he heq m

lemma kernel_one_shift_bounds {n q : ℕ} {u R : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hR : 0 < R) (hphase : Real.sqrt R*Real.sqrt u < Real.pi/2)
    (b v : ℕ → ℝ) (hb : Monotone (fun i : Fin (n+1)=>b i)) (hball : ∀ i,0 ≤ b i ∧ b i ≤ R)
    (hq : q ≤ n) (hbzero : ∀ i,i ≤ q → b i=0) (hv : ∀ i,0 < v i)
    (hx : ∀ i : Fin (n+1),u ≤ v i) (hord : StrictMono (fun i : Fin (n+1)=>v i)) (m : ℕ) :
    (1/2:ℝ)*poleProduct v (shiftedPole u 0) (n+1) ≤ kernelOriginFunctional (n:=n+1) b u v (fun y=>1-oneShiftProduct u m y) ∧
    kernelOriginFunctional (n:=n+1) b u v (fun y=>1-oneShiftProduct u m y) ≤ 2*poleProduct v (shiftedPole u 0) (q+1) := by
  apply kernel_origin_bounds hu hR hphase b v _ hb hball hq hbzero (fun i=>hv i) hx hord
  intro e he heq
  exact sparse_one_shift_bounds hu hu4 v e hv hord he heq m

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional
open Finset Filter Topology

lemma C_ofReal_re (t x : ℝ) : ((C t x).re:ℂ)=C t x := by
  unfold C
  split_ifs
  · rfl
  · rfl
lemma hZero_ofReal_re (x : ℝ) : ((hZero x).re:ℂ)=hZero x := by
  have h : D x=(((D x).re):ℂ) := by
    unfold D
    rw [←C_ofReal_re angle x]
    norm_num [Complex.mul_re,Complex.sub_re]
  unfold hZero
  rw [h]
  simp
lemma hOne_ofReal_re (x : ℝ) : ((hOne x).re:ℂ)=hOne x := by
  change (((C (angle/2) x*hZero x).re):ℂ)=C (angle/2) x*hZero x
  rw [←C_ofReal_re (angle/2) x,←hZero_ofReal_re x]
  simp
lemma hZero_re_pos {x : ℝ} (hx : -4 ≤ x) : 0 < (hZero x).re := by
  rw [hZero_cosh_ratio hx,←C_ofReal_re (angle/2) x,←C_ofReal_re (3*angle/2) x,
    ←Complex.ofReal_div,Complex.ofReal_re]
  exact div_pos (C_re_pos (by linarith [angle_pos]) (half_angle_pole_condition hx))
    (C_re_pos (by linarith [angle_pos]) (three_half_angle_pole_condition hx))
lemma hOne_re_pos {x : ℝ} (hx : -4 ≤ x) : 0 < (hOne x).re := by
  rw [hOne_cosh_ratio hx,←C_ofReal_re (angle/2) x,←C_ofReal_re (3*angle/2) x,
    ←Complex.ofReal_pow,←Complex.ofReal_div,Complex.ofReal_re]
  exact div_pos (sq_pos_of_pos (C_re_pos (by linarith [angle_pos]) (half_angle_pole_condition hx)))
    (C_re_pos (by linarith [angle_pos]) (three_half_angle_pole_condition hx))

namespace StripAsymptotic

lemma shiftedPole_normalization {u y : ℝ} {n : ℕ} (hu4 : u ≤ 4) (hy : 0 ≤ y) :
    ((shiftedPole u n/(shiftedPole u n+y):ℝ):ℂ)=poleFactor n (-u)/poleFactor n (y-u) := by
  have hn : (physicalPole n:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (physicalPole_pos n).ne'
  have hd : ((physicalPole n-u+y:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith [physicalPole_ge n]))
  unfold shiftedPole poleFactor
  push_cast at hd ⊢
  have hd2 : (physicalPole n:ℂ)+((y:ℂ)-u) ≠ 0 := by convert hd using 1 ; ring
  field_simp [hn,hd,hd2]
  ; ring

lemma shiftedNumerator_normalization {u y : ℝ} (hu4 : u ≤ 4) (n : ℕ) :
    ((1+y/(shiftedPole u n):ℝ):ℂ)=poleFactor n (y-u)/poleFactor n (-u) := by
  have hn : (physicalPole n:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (physicalPole_pos n).ne'
  have hd : ((physicalPole n-u:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (shiftedPole_pos hu4 n).ne'
  unfold shiftedPole poleFactor
  push_cast at hd ⊢
  have hd2 : (physicalPole n:ℂ)+ -(u:ℂ) ≠ 0 := by simpa only [sub_eq_add_neg] using hd
  field_simp [hn,hd,hd2]
  ; ring

lemma pair_shift_ratio {u y : ℝ} (hu4 : u ≤ 4) (hy : 0 ≤ y) (n : ℕ) :
    (((physicalPairExpr u n).eval y):ℂ)=
      (poleFactor (3*n) (y-u)*poleFactor (3*n+2) (y-u))⁻¹ /
      (poleFactor (3*n) (-u)*poleFactor (3*n+2) (-u))⁻¹ := by
  rw [physicalPairExpr,ReciprocalExpr.mulExpr_eval,ReciprocalExpr.normalizedPole_eval,
    ReciprocalExpr.normalizedPole_eval,Complex.ofReal_mul,shiftedPole_normalization hu4 hy,
    shiftedPole_normalization hu4 hy]
  simp only [inv_div_inv,mul_div_mul_comm]
lemma triple_shift_ratio {u y : ℝ} (hu4 : u ≤ 4) (hy : 0 ≤ y) (n : ℕ) :
    (((physicalTripleExpr u n).eval y):ℂ)=
      (poleFactor (3*n+1) (y-u)/(poleFactor (3*n) (y-u)*poleFactor (3*n+2) (y-u))) /
      (poleFactor (3*n+1) (-u)/(poleFactor (3*n) (-u)*poleFactor (3*n+2) (-u))) := by
  rw [physicalTripleExpr,ReciprocalExpr.tripleFactor_eval (shiftedPole_pos hu4 _)
    (shiftedPole_strictMono u (by omega)) (shiftedPole_strictMono u (by omega))
    (ne_of_gt (add_pos_of_pos_of_nonneg (shiftedPole_pos hu4 _) hy))
    (ne_of_gt (add_pos_of_pos_of_nonneg (shiftedPole_pos hu4 _) hy))]
  rw [Complex.ofReal_mul,Complex.ofReal_mul,shiftedNumerator_normalization hu4,
    shiftedPole_normalization hu4 hy,shiftedPole_normalization hu4 hy]
  field_simp


lemma zeroShiftProduct_eq_prod (u y : ℝ) (m : ℕ) :
    zeroShiftProduct u m y=∏ j ∈ range (m+1),(physicalPairExpr u j).eval y := by
  rw [prod_range_succ']
  simp only [zeroShiftProduct,physicalPairTail,ReciprocalExpr.rangeProduct_eval,
    physicalPairExpr,Nat.mul_zero,Nat.zero_add,ReciprocalExpr.mulExpr_eval,
    ReciprocalExpr.normalizedPole_eval]
  ring
lemma oneShiftProduct_eq_prod (u y : ℝ) (m : ℕ) :
    oneShiftProduct u m y=∏ j ∈ range (m+1),(physicalTripleExpr u j).eval y := by
  rw [prod_range_succ']
  simp only [oneShiftProduct,physicalTripleTail,ReciprocalExpr.rangeProduct_eval]
  ring

lemma zeroShiftProduct_ratio {u y : ℝ} (hu4 : u ≤ 4) (hy : 0 ≤ y) (m : ℕ) :
    ((zeroShiftProduct u m y):ℂ)=hZeroProduct (m+1) (y-u)/hZeroProduct (m+1) (-u) := by
  rw [zeroShiftProduct_eq_prod,Complex.ofReal_prod]
  simp only [pair_shift_ratio hu4 hy,prod_div_distrib,hZeroProduct]
lemma oneShiftProduct_ratio {u y : ℝ} (hu4 : u ≤ 4) (hy : 0 ≤ y) (m : ℕ) :
    ((oneShiftProduct u m y):ℂ)=hOneProduct (m+1) (y-u)/hOneProduct (m+1) (-u) := by
  rw [oneShiftProduct_eq_prod,Complex.ofReal_prod]
  simp only [triple_shift_ratio hu4 hy,prod_div_distrib,hOneProduct]

lemma tendsto_zeroShiftProduct {u y : ℝ} (hu4 : u ≤ 4) (hy : 0 ≤ y) :
    Tendsto (fun m=>zeroShiftProduct u m y) atTop (𝓝 ((hZero (y-u)).re/(hZero (-u)).re)) := by
  have h:=((tendsto_hZeroProduct (by linarith : -4 ≤ y-u)).div
    (tendsto_hZeroProduct (by linarith : -4 ≤ -u))
    (by rw [←hZero_ofReal_re (-u)];exact Complex.ofReal_ne_zero.mpr (hZero_re_pos (by linarith)).ne')).comp
      (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def,Pi.div_apply,←zeroShiftProduct_ratio hu4 hy] at h
  have hr:=Complex.continuous_re.continuousAt.tendsto.comp h
  have he : (hZero (y-u)/hZero (-u)).re=(hZero (y-u)).re/(hZero (-u)).re := by
    conv_lhs => rw [←hZero_ofReal_re (y-u),←hZero_ofReal_re (-u),←Complex.ofReal_div,Complex.ofReal_re]
  simpa only [Function.comp_def,Complex.ofReal_re,he] using hr
lemma tendsto_oneShiftProduct {u y : ℝ} (hu4 : u ≤ 4) (hy : 0 ≤ y) :
    Tendsto (fun m=>oneShiftProduct u m y) atTop (𝓝 ((hOne (y-u)).re/(hOne (-u)).re)) := by
  have h:=((tendsto_hOneProduct (by linarith : -4 ≤ y-u)).div
    (tendsto_hOneProduct (by linarith : -4 ≤ -u))
    (by rw [←hOne_ofReal_re (-u)];exact Complex.ofReal_ne_zero.mpr (hOne_re_pos (by linarith)).ne')).comp
      (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def,Pi.div_apply,←oneShiftProduct_ratio hu4 hy] at h
  have hr:=Complex.continuous_re.continuousAt.tendsto.comp h
  have he : (hOne (y-u)/hOne (-u)).re=(hOne (y-u)).re/(hOne (-u)).re := by
    conv_lhs => rw [←hOne_ofReal_re (y-u),←hOne_ofReal_re (-u),←Complex.ofReal_div,Complex.ofReal_re]
  simpa only [Function.comp_def,Complex.ofReal_re,he] using hr

end StripAsymptotic
end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Filter Topology Matrix

lemma kernelOriginFunctional_tendsto {n : ℕ} (b v : ℕ → ℝ) (a : ℝ)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ i : Fin n,Tendsto (fun m=>f m (v i)) atTop (𝓝 (g (v i)))) :
    Tendsto (fun m=>kernelOriginFunctional (n:=n) b a v (f m)) atTop
      (𝓝 (kernelOriginFunctional (n:=n) b a v g)) := by
  have ht : Tendsto (fun m=>kernelComplementMatrix (n:=n) b a v (f m)) atTop
      (𝓝 (kernelComplementMatrix (n:=n) b a v g)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_const_nhds.add ((hf j |>.sub_const 1).const_mul _)
  have hd : Continuous (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) := continuous_id.matrix_det
  exact (hd.continuousAt.tendsto.comp ht).div_const _


lemma kernel_hZero_bounds {n q : ℕ} {u R : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hR : 0 < R) (hphase : Real.sqrt R*Real.sqrt u < Real.pi/2)
    (b v : ℕ → ℝ) (hb : Monotone (fun i : Fin (n+1)=>b i)) (hball : ∀ i,0 ≤ b i ∧ b i ≤ R)
    (hq : q ≤ n) (hbzero : ∀ i,i ≤ q → b i=0) (hv : ∀ i,0 < v i)
    (hx : ∀ i : Fin (n+1),u ≤ v i) (hord : StrictMono (fun i : Fin (n+1)=>v i)) :
    poleProduct v (shiftedPole u 0) (n+1) ≤
      kernelOriginFunctional (n:=n+1) b u v (fun y=>1-(hZero (y-u)).re/(hZero (-u)).re) ∧
    kernelOriginFunctional (n:=n+1) b u v (fun y=>1-(hZero (y-u)).re/(hZero (-u)).re) ≤
      2*poleProduct v (shiftedPole u 0) (q+1) := by
  have ht := kernelOriginFunctional_tendsto (n:=n+1) b v u
    (fun m y=>1-zeroShiftProduct u m y) (fun y=>1-(hZero (y-u)).re/(hZero (-u)).re)
    (fun i=>tendsto_const_nhds.sub (tendsto_zeroShiftProduct hu4 (hv i).le))
  have h m := kernel_zero_shift_bounds hu hu4 hR hphase b v hb hball hq hbzero hv hx hord m
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall (fun m=>(h m).1)),
    le_of_tendsto_of_tendsto ht tendsto_const_nhds (Eventually.of_forall (fun m=>(h m).2))⟩

lemma kernel_hOne_bounds {n q : ℕ} {u R : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hR : 0 < R) (hphase : Real.sqrt R*Real.sqrt u < Real.pi/2)
    (b v : ℕ → ℝ) (hb : Monotone (fun i : Fin (n+1)=>b i)) (hball : ∀ i,0 ≤ b i ∧ b i ≤ R)
    (hq : q ≤ n) (hbzero : ∀ i,i ≤ q → b i=0) (hv : ∀ i,0 < v i)
    (hx : ∀ i : Fin (n+1),u ≤ v i) (hord : StrictMono (fun i : Fin (n+1)=>v i)) :
    (1/2:ℝ)*poleProduct v (shiftedPole u 0) (n+1) ≤
      kernelOriginFunctional (n:=n+1) b u v (fun y=>1-(hOne (y-u)).re/(hOne (-u)).re) ∧
    kernelOriginFunctional (n:=n+1) b u v (fun y=>1-(hOne (y-u)).re/(hOne (-u)).re) ≤
      2*poleProduct v (shiftedPole u 0) (q+1) := by
  have ht := kernelOriginFunctional_tendsto (n:=n+1) b v u
    (fun m y=>1-oneShiftProduct u m y) (fun y=>1-(hOne (y-u)).re/(hOne (-u)).re)
    (fun i=>tendsto_const_nhds.sub (tendsto_oneShiftProduct hu4 (hv i).le))
  have h m := kernel_one_shift_bounds hu hu4 hR hphase b v hb hball hq hbzero hv hx hord m
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall (fun m=>(h m).1)),
    le_of_tendsto_of_tendsto ht tendsto_const_nhds (Eventually.of_forall (fun m=>(h m).2))⟩

lemma source_translation_phase {u : ℝ} (hu4 : u ≤ 4) :
    Real.sqrt (angle^2)*Real.sqrt u < Real.pi/2 := by
  rw [Real.sqrt_sq angle_pos.le]
  have hu : Real.sqrt u ≤ 2 := by
    have h := Real.sqrt_le_sqrt hu4
    norm_num at h
    exact h
  have hp:=Real.pi_pos
  calc
    angle*Real.sqrt u ≤ angle*2 := mul_le_mul_of_nonneg_left hu angle_pos.le
    _ < Real.pi/2 := by unfold angle; linarith

/-- Physical sorted flag specialization; all original confluent nodes remain. -/
lemma source_hZero_kernel_bounds {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) {t : ℝ} (ht : 0<t) (htL : t<angle)
    (x : ℕ → ℝ) (hx : ∀ i,0<x i) (hord : StrictMono (fun i : Fin (2*N+1)=>x i)) :
    poleProduct (fun j=>x j+u) (shiftedPole u 0) (2*N+1) ≤
      kernelOriginFunctional (n:=2*N+1) (interiorKnotLabels N t) u (fun j=>x j+u)
        (fun y=>1-(hZero (y-u)).re/(hZero (-u)).re) ∧
    kernelOriginFunctional (n:=2*N+1) (interiorKnotLabels N t) u (fun j=>x j+u)
        (fun y=>1-(hZero (y-u)).re/(hZero (-u)).re) ≤
      2*poleProduct (fun j=>x j+u) (shiftedPole u 0) N := by
  have h := kernel_hZero_bounds (n:=2*N) (q:=N-1) hu hu4 (sq_pos_of_pos angle_pos)
    (source_translation_phase hu4) (interiorKnotLabels N t) (fun j=>x j+u)
    (fun _ _ hij=>interiorKnot_monotone N ht htL hij)
    (fun i=>⟨interiorKnot_nonneg N i t,interiorKnot_le N i ht htL⟩)
    (by omega) (by intro i hi; simp [interiorKnotLabels,show i<N by omega])
    (fun i=>add_pos_of_pos_of_nonneg (hx i) hu)
    (fun i=>by linarith [hx i]) (fun i j hij=>by linarith [hord hij])
  have he : N-1+1=N := by omega
  simpa only [he] using h

lemma source_hOne_kernel_bounds {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) {t : ℝ} (ht : 0<t) (htL : t<angle)
    (x : ℕ → ℝ) (hx : ∀ i,0<x i) (hord : StrictMono (fun i : Fin (2*N+1)=>x i)) :
    (1/2:ℝ)*poleProduct (fun j=>x j+u) (shiftedPole u 0) (2*N+1) ≤
      kernelOriginFunctional (n:=2*N+1) (interiorKnotLabels N t) u (fun j=>x j+u)
        (fun y=>1-(hOne (y-u)).re/(hOne (-u)).re) ∧
    kernelOriginFunctional (n:=2*N+1) (interiorKnotLabels N t) u (fun j=>x j+u)
        (fun y=>1-(hOne (y-u)).re/(hOne (-u)).re) ≤
      2*poleProduct (fun j=>x j+u) (shiftedPole u 0) N := by
  have h := kernel_hOne_bounds (n:=2*N) (q:=N-1) hu hu4 (sq_pos_of_pos angle_pos)
    (source_translation_phase hu4) (interiorKnotLabels N t) (fun j=>x j+u)
    (fun _ _ hij=>interiorKnot_monotone N ht htL hij)
    (fun i=>⟨interiorKnot_nonneg N i t,interiorKnot_le N i ht htL⟩)
    (by omega) (by intro i hi; simp [interiorKnotLabels,show i<N by omega])
    (fun i=>add_pos_of_pos_of_nonneg (hx i) hu)
    (fun i=>by linarith [hx i]) (fun i j hij=>by linarith [hord hij])
  have he : N-1+1=N := by omega
  simpa only [he] using h

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
