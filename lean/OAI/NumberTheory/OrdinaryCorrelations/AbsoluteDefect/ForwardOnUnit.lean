import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ForwardSum

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

namespace OrdinaryRoughBridge
open OrdinaryCorrelations SourceRoughFourier OrdinaryInitialWidth OrdinaryLocalAdditive Finset MeasureTheory

lemma forward_on_unit (f : ℕ→ℂ) (α : ℝ) (D v : ℕ) {x : ℝ}
    (hx : x∈Set.Ioo (v:ℝ) ((v:ℝ)+1)) :
    forwardSum f α D x = ∑m∈Icc 1 D,f (v+m)*phase (α*(v+m)) := by
  have hx0 : 0≤x := (Nat.cast_nonneg v).trans hx.1.le
  have hf : ⌊x⌋₊=v := (Nat.floor_eq_iff hx0).mpr ⟨hx.1.le,hx.2⟩
  have hfd : ⌊x+(D:ℝ)⌋₊=v+D := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> push_cast <;> linarith [hx.1,hx.2]
  unfold forwardSum
  rw [hf,hfd]
  symm
  refine sum_bij (fun m _=>v+m) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_Icc,Finset.mem_Ioc] at hm ⊢; omega
  · intro m hm n hn he; omega
  · intro n hn
    refine ⟨n-v,?_,?_⟩ <;> simp only [Finset.mem_Icc,Finset.mem_Ioc] at hn ⊢ <;> omega
  · intro m hm; simp only [Nat.cast_add]

lemma forward_discrete_le_integral (f : ℕ→ℂ) (α : ℝ) (D U : ℕ) :
    (∑v∈Icc 1 U,‖∑m∈Icc 1 D,f (v+m)*phase (α*(v+m))‖) ≤
      ∫x in Set.Ioc 0 ((U:ℝ)+1),‖forwardSum f α D x‖ := by
  have hint (v : ℕ) : IntervalIntegrable (fun x=>‖forwardSum f α D x‖)
      volume (v:ℝ) ((v:ℝ)+1) := by
    apply (intervalIntegrable_const (c:=‖∑m∈Icc 1 D,f (v+m)*phase (α*(v+m))‖)).congr_uIoo
    rw [Set.uIoo_of_le (by linarith : (v:ℝ)≤(v:ℝ)+1)]
    intro x hx; exact (congrArg norm (forward_on_unit f α D v hx)).symm
  have he (v : ℕ) : (∫x in (v:ℝ)..((v:ℝ)+1),‖forwardSum f α D x‖) =
      ‖∑m∈Icc 1 D,f (v+m)*phase (α*(v+m))‖ := by
    calc
      _ = ∫_x in (v:ℝ)..((v:ℝ)+1),‖∑m∈Icc 1 D,f (v+m)*phase (α*(v+m))‖ := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro x hx; exact congrArg norm (forward_on_unit f α D v hx)
      _ = _ := by simp
  calc
    _ ≤ ∑v∈range (U+1),‖∑m∈Icc 1 D,f (v+m)*phase (α*(v+m))‖ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro v hv; simp only [Finset.mem_Icc,Finset.mem_range] at hv ⊢; omega
      · intro v hv hv'; exact norm_nonneg _
    _ = ∑v∈range (U+1),∫x in (v:ℝ)..((v:ℝ)+1),‖forwardSum f α D x‖ := by
      apply sum_congr rfl; intro v hv; exact (he v).symm
    _ = ∫x in (0:ℝ)..((U:ℝ)+1),‖forwardSum f α D x‖ := by
      convert intervalIntegral.sum_integral_adjacent_intervals
        (a:=fun v:ℕ=>(v:ℝ)) (n:=U+1) (f:=fun x=>‖forwardSum f α D x‖)
        (fun v hv=>by simpa using hint v) using 1 <;> simp
    _ = _ := intervalIntegral.integral_of_le (by positivity)

variable {N : ℕ} [NeZero N]
lemma stdAddChar_phase (m : ℕ) (k : ZMod N) :
    ZMod.stdAddChar ((m:ZMod N)*k)=phase ((k.val:ℝ)/N*m) := by
  have he : (m:ZMod N)*k=((m*k.val:ℕ):ZMod N) := by simp
  rw [he,←Int.cast_natCast,ZMod.stdAddChar_coe]
  unfold phase
  congr 1
  push_cast
  ring

lemma shifted_norm (f : ℕ→ℂ) (α : ℝ) (D v : ℕ) :
    ‖∑m∈Icc 1 D,f (v+m)*phase (α*m)‖ =
      ‖∑m∈Icc 1 D,f (v+m)*phase (α*(v+m))‖ := by
  have he : (∑m∈Icc 1 D,f (v+m)*phase (α*(v+m))) =
      phase (α*v)*(∑m∈Icc 1 D,f (v+m)*phase (α*m)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [mul_add,phase_add]
    ring
  rw [he,norm_mul,norm_phase,one_mul]

lemma grid_short_le_forward (f : ℕ→ℂ) (D U : ℕ) (k : ZMod N) :
    (∑v∈Icc 1 U,‖poly (Icc 1 D) (fun m=>f (v+m)) (fun m=>(m:ZMod N)) k‖) ≤
      ∫x in Set.Ioc 0 ((U:ℝ)+1),‖forwardSum f ((k.val:ℝ)/N) D x‖ := by
  simp only [poly,stdAddChar_phase]
  simp_rw [shifted_norm]
  exact forward_discrete_le_integral f _ D U

lemma grid_neg_short_le_forward (f : ℕ→ℂ) (D U : ℕ) (k : ZMod N) :
    (∑v∈Icc 1 U,‖poly (Icc 1 D) (fun m=>f (v+m)) (fun m=> -(m:ZMod N)) k‖) ≤
      ∫x in Set.Ioc 0 ((U:ℝ)+1),‖forwardSum f (((-k).val:ℝ)/N) D x‖ := by
  have he : ∀v,poly (Icc 1 D) (fun m=>f (v+m)) (fun m=> -(m:ZMod N)) k=
      poly (Icc 1 D) (fun m=>f (v+m)) (fun m=>(m:ZMod N)) (-k) := by
    intro v; simp only [poly,neg_mul,mul_neg]
  simp_rw [he]
  exact grid_short_le_forward f D U (-k)

end OrdinaryRoughBridge

end

end OAI
