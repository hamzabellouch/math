import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BetaZ
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ClosedLine
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrimeSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VertexWeight
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.KappaPos
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CardTreeVerticesLe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LabelPrimeSet

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Finset Classical
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace
open Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ T : ℝ} {h ℓ : ℕ}

def divisorPrimeFactor (S : PrimeSystem) (r : S.Residues) (b : ℤ) (p : S.Index) : ℝ :=
  if S.IsCore p then A*activity p (r p) b else activity p (r p) b-theta/(p:ℝ)

def divisorEdgeWeight (S : PrimeSystem) (cut : S.Cutoffs T) (r : S.Residues)
    (d : ℕ) (b c : ℤ) : ℝ :=
  cut.value d (S.shiftCore (S.restrictCore r) b)*
    cut.value d (S.shiftCore (S.restrictCore r) c)*
      ∏ p : S.Index, if (p:ℕ)∣d then S.divisorPrimeFactor r b p else 1

lemma divisorEdgeWeight_eq_edgeWeight (w : ClosedLine h ℓ) (cut : S.Cutoffs T)
    (r : S.Residues) (i : Fin ℓ) :
    S.divisorEdgeWeight cut r (w.label i) (w.offset i.castSucc) (w.offset i.succ)=
      S.edgeWeight w cut r i := by
  unfold divisorEdgeWeight edgeWeight
  rfl

lemma divisor_factor_product (D : S.DivisorFamily B τ C₀) (d : ℕ) (hd : d∈D.members)
    (r : S.Residues) (b : ℤ) :
    (∏ p : S.Index,if (p:ℕ)∣d then |S.divisorPrimeFactor r b p| else 1)=
      ∏ p∈labelPrimeSet d hd,|S.divisorPrimeFactor r b p| := by
  rw [←prod_filter]
  congr 1
  ext p
  simp only [mem_filter,mem_labelPrimeSet,Nat.mem_primeFactors]
  have hp := S.prime_mem p p.property
  have hd0 : d≠0 := ne_of_gt (lt_trans zero_lt_one (D.greater_one d hd))
  simp [hp,hd0]

lemma divisorEdgeWeight_abs_le (D : S.DivisorFamily B τ C₀) (d : ℕ) (hd : d∈D.members)
    (cut : S.Cutoffs T) (r : S.Residues) (b c : ℤ) :
    |S.divisorEdgeWeight cut r d b c| ≤
      ∏ p∈labelPrimeSet d hd,|S.divisorPrimeFactor r b p| := by
  unfold divisorEdgeWeight
  rw [abs_mul,abs_mul,abs_of_nonneg (cut.nonneg _ _),abs_of_nonneg (cut.nonneg _ _),
    abs_prod]
  have he : (∏ p : S.Index, |if (p:ℕ)∣d then S.divisorPrimeFactor r b p else 1|)=
      ∏ p∈labelPrimeSet d hd,|S.divisorPrimeFactor r b p| := by
    simp_rw [apply_ite abs,abs_one]
    exact divisor_factor_product D d hd r b
  rw [he]
  have hc : cut.value d (S.shiftCore (S.restrictCore r) b)*
      cut.value d (S.shiftCore (S.restrictCore r) c) ≤ 1 := by
    simpa using mul_le_mul (cut.le_one _ _) (cut.le_one _ _) (cut.nonneg _ _) zero_le_one
  simpa using mul_le_mul_of_nonneg_right hc (prod_nonneg (fun p hp => abs_nonneg _))

lemma divisor_degree_euler (D : S.DivisorFamily B τ C₀) (cut : S.Cutoffs T)
    (r : S.Residues) (b : ℤ) (c : ℕ → ℤ) :
    (∑ d∈D.members,|S.divisorEdgeWeight cut r d b (c d)|) ≤
      ∏ p : S.Index,(1+|S.divisorPrimeFactor r b p|) := by
  rw [prod_one_add]
  rw [←sum_attach D.members (fun d => |S.divisorEdgeWeight cut r d b (c d)|)]
  let enc : {d // d∈D.members} → Finset S.Index := fun d => labelPrimeSet d.val d.property
  have hinj : Function.Injective enc := by
    intro d e he
    apply Subtype.ext
    have hp := congrArg (fun u : Finset S.Index => ∏ p∈u,p.val) he
    simpa only [enc,labelPrimeSet_product] using hp
  calc
    _ ≤ ∑ d∈D.members.attach,∏ p∈enc d,|S.divisorPrimeFactor r b p| := by
      apply sum_le_sum
      intro d hd
      exact divisorEdgeWeight_abs_le D d d.property cut r b (c d)
    _ = ∑ E∈D.members.attach.image enc,∏ p∈E,|S.divisorPrimeFactor r b p| :=
      (sum_image (f:=fun E : Finset S.Index => ∏ p∈E,|S.divisorPrimeFactor r b p|)
        (s:=D.members.attach) (g:=enc) (fun d hd e he hde => hinj hde)).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro E hE
        exact mem_powerset.mpr (subset_univ _)
      · intro E hE hn
        exact prod_nonneg (fun p hp => abs_nonneg _)

lemma divisor_prime_factor_bound (r : S.Residues) (b : ℤ) (p : S.Index) :
    1+|S.divisorPrimeFactor r b p| ≤
      (S.beta p)⁻¹^(if r p+(b:ZMod (p:ℕ))=0 then (1:ℕ) else 0)*
      Real.exp (if S.IsCore p then 0 else theta/(p:ℝ)) := by
  have hp : (2:ℝ)≤(p:ℝ) := by exact_mod_cast (S.prime_mem p p.property).two_le
  have hp0 : (0:ℝ)<(p:ℝ) := by linarith
  have hx0 : 0≤theta/(p:ℝ) := by rw [theta_value]; positivity
  have hx1 : theta/(p:ℝ)≤1 := by rw [div_le_one hp0,theta_value]; linarith
  have he0 : 1≤Real.exp (theta/(p:ℝ)) := Real.one_le_exp hx0
  by_cases hc : S.IsCore p
  · by_cases ha : r p+(b:ZMod (p:ℕ))=0
    · simp [divisorPrimeFactor,hc,activity,ha,beta,amplitude,abs_of_pos A_pos]
    · simp [divisorPrimeFactor,hc,activity,ha,beta,amplitude]
  · by_cases ha : r p+(b:ZMod (p:ℕ))=0
    · simp only [divisorPrimeFactor,hc,ite_false,activity,ha,ite_true,pow_one,beta,amplitude,inv_inv]
      rw [abs_of_nonneg (sub_nonneg.mpr hx1)]
      nlinarith
    · simp only [divisorPrimeFactor,hc,ite_false,activity,ha,pow_zero,one_mul,zero_sub,abs_neg,
        abs_of_nonneg hx0]
      simpa only [add_comm] using Real.add_one_le_exp (theta/(p:ℝ))

theorem divisor_absolute_degree (D : S.DivisorFamily B τ C₀) (cut : S.Cutoffs T)
    (r : S.Residues) (b : ℤ) (c : ℕ → ℤ) :
    (∑ d∈D.members,|S.divisorEdgeWeight cut r d b (c d)|) ≤
      S.vertexWeight r b*Real.exp (theta*S.harmonicCenter) := by
  apply (divisor_degree_euler D cut r b c).trans
  calc
    _ ≤ ∏ p : S.Index,(S.beta p)⁻¹^(if r p+(b:ZMod (p:ℕ))=0 then (1:ℕ) else 0)*
        Real.exp (if S.IsCore p then 0 else theta/(p:ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        positivity
      · intro p hp
        exact divisor_prime_factor_bound r b p
    _ = _ := by
      rw [prod_mul_distrib,←Real.exp_sum]
      congr 2
      have he := sum_subtype (F:=inferInstance) (p:=fun p : S.Index => ¬S.IsCore p)
        (univ.filter (fun p : S.Index => ¬S.IsCore p)) (by simp)
        (fun p : S.Index => (p:ℝ)⁻¹)
      have hef : (∑ p : S.Index,if S.IsCore p then (0:ℝ) else (p:ℝ)⁻¹)=S.harmonicCenter := by
        simpa only [sum_filter,harmonicCenter,ite_not] using he
      rw [←hef,mul_sum]
      apply sum_congr rfl
      intro p hp
      split_ifs <;> simp [div_eq_mul_inv]

lemma divisorPrimeFactor_eq_of_dvd (r : S.Residues) (b c : ℤ) (p : S.Index)
    (hd : ((p:ℕ):ℤ)∣c-b) : S.divisorPrimeFactor r b p=S.divisorPrimeFactor r c p := by
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (c-b) (p:ℕ)).mpr hd
  rw [Int.cast_sub,sub_eq_zero] at hz
  simp only [divisorPrimeFactor,activity,hz]

lemma divisorEdgeWeight_symm (cut : S.Cutoffs T) (r : S.Residues) (d : ℕ) (b c : ℤ)
    (hd : (d:ℤ)∣c-b) :
    S.divisorEdgeWeight cut r d b c=S.divisorEdgeWeight cut r d c b := by
  unfold divisorEdgeWeight
  rw [mul_comm (cut.value d (S.shiftCore (S.restrictCore r) b))]
  congr 1
  apply prod_congr rfl
  intro p hp
  split_ifs with hpd
  · exact divisorPrimeFactor_eq_of_dvd r b c p (dvd_trans (by exact_mod_cast hpd) hd)
  · rfl

theorem incoming_divisor_absolute_degree (D : S.DivisorFamily B τ C₀) (cut : S.Cutoffs T)
    (r : S.Residues) (b : ℤ) (c : ℕ → ℤ) (hc : ∀ d∈D.members,(d:ℤ)∣b-c d) :
    (∑ d∈D.members,|S.divisorEdgeWeight cut r d (c d) b|) ≤
      S.vertexWeight r b*Real.exp (theta*S.harmonicCenter) := by
  have he : (∑ d∈D.members,|S.divisorEdgeWeight cut r d (c d) b|)=
      ∑ d∈D.members,|S.divisorEdgeWeight cut r d b (c d)| := by
    apply sum_congr rfl
    intro d hd
    rw [divisorEdgeWeight_symm cut r d (c d) b (hc d hd)]
  rw [he]
  exact divisor_absolute_degree D cut r b c

lemma vertexWeight_pos (r : S.Residues) (b : ℤ) : 0<S.vertexWeight r b := by
  unfold vertexWeight
  apply prod_pos
  intro p hp
  apply pow_pos
  rw [inv_pos,beta,inv_pos]
  unfold amplitude
  split_ifs <;> linarith [A_pos]

lemma closedLine_sqrt_weight_products (w : ClosedLine h ℓ) (r : S.Residues) :
    (∏ i : Fin ℓ,Real.sqrt (S.vertexWeight r (w.offset i.succ)))=
      ∏ i : Fin ℓ,Real.sqrt (S.vertexWeight r (w.offset i.castSucc)) := by
  have h₁ := Fin.prod_univ_succ (fun i : Fin (ℓ+1) => Real.sqrt (S.vertexWeight r (w.offset i)))
  have h₂ := Fin.prod_univ_castSucc (fun i : Fin (ℓ+1) => Real.sqrt (S.vertexWeight r (w.offset i)))
  rw [w.start_zero] at h₁
  rw [w.end_zero] at h₂
  have he := h₁.symm.trans h₂
  rw [mul_comm _ (Real.sqrt (S.vertexWeight r 0))] at he
  exact mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (vertexWeight_pos r 0))) he

lemma closedLine_sqrtWeight_product (w : ClosedLine h ℓ) (r : S.Residues) :
    (∏ i : Fin ℓ,Real.sqrt (S.vertexWeight r (w.offset i.castSucc)*
      S.vertexWeight r (w.offset i.succ)))=∏ i : Fin ℓ,S.vertexWeight r (w.offset i.castSucc) := by
  simp_rw [Real.sqrt_mul (vertexWeight_pos r _).le]
  rw [prod_mul_distrib,closedLine_sqrt_weight_products,←pow_two,←Finset.prod_pow]
  apply prod_congr rfl
  intro i hi
  exact Real.sq_sqrt (vertexWeight_pos r _).le

theorem normalized_closedLine_product (w : ClosedLine h ℓ) (cut : S.Cutoffs T)
    (r : S.Residues) :
    (∏ i : Fin ℓ,S.divisorEdgeWeight cut r (w.label i) (w.offset i.castSucc) (w.offset i.succ)/
      Real.sqrt (S.vertexWeight r (w.offset i.castSucc)*S.vertexWeight r (w.offset i.succ)))=
      S.chronologicalKernel w cut r := by
  simp_rw [divisorEdgeWeight_eq_edgeWeight]
  rw [prod_div_distrib,closedLine_sqrtWeight_product]
  simp only [chronologicalKernel,prod_div_distrib]

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
