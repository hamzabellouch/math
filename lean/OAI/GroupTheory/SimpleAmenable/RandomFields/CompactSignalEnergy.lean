import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.DyadicArithmetic
import OAI.GroupTheory.SimpleAmenable.RandomFields.PolygonApproxIdentity

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CompactSignalEnergy
open Classical

theorem compactSignal_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ) (q : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀N : ℝ,1≤N → ∀T : Finset (FlagSite a m D v),
      ∑z∈T,(flagSignalDifference hD g (fun x => q+ψ x) N z)^2 ≤ C^2 := by
  obtain ⟨K,hK,hcompact⟩ := hs.exists_pos_le_norm
  obtain ⟨L₀,L₁,hL₀,hL₁⟩ := compactSignal_uniform_constants ψ hψ hs
  obtain ⟨C,hC,henergy⟩ := flagSignalDifference_energy (v:=v) hD g (fun x => q+ψ x) hK
    (by intro x hx; rw [hcompact x hx,add_zero]) L₀.coe_nonneg (by
      intro x y
      simp only [add_sub_add_left_eq_sub]
      have hh := hL₀.dist_le_mul x y
      rw [Real.dist_eq,dist_eq_norm,Prod.norm_def] at hh
      refine hh.trans (mul_le_mul_of_nonneg_left ?_ L₀.coe_nonneg)
      simp only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _)))
  refine ⟨Real.sqrt C,Real.sqrt_nonneg _,?_⟩
  simpa only [Real.sq_sqrt hC] using henergy

end CompactSignalEnergy

section SourceSignalScales
open Classical Filter
open scoped Topology

noncomputable def sourceDyadicMass (n : ℕ) : ℝ :=
  sourceDyadicWeight n*((sourceDyadicIndices n).card:ℝ)

theorem sourceDyadicWeight_nonneg (n : ℕ) : 0 ≤ sourceDyadicWeight n :=
  Real.rpow_nonneg (Real.log_nonneg (sourceDyadicN_one_le n)) _

theorem sourceDyadicMass_nonneg (n : ℕ) : 0 ≤ sourceDyadicMass n :=
  mul_nonneg (sourceDyadicWeight_nonneg n) (Nat.cast_nonneg _)

theorem sourceDyadicMass_tendsto : Tendsto sourceDyadicMass atTop atTop := by
  let c := (4*Real.log 2)^(-3/4:ℝ)
  have hc : 0<c := by dsimp [c]; positivity
  have ht : Tendsto (fun n : ℕ => c*(n:ℝ)^(1/4:ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (show (0:ℝ)<1/4 by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hw : sourceDyadicWeight n=c*(n:ℝ)^(-3/4:ℝ) := by
    unfold sourceDyadicWeight
    rw [sourceDyadic_log,Real.mul_rpow (by positivity) (Nat.cast_nonneg n)]
  have he : (n:ℝ)*(n:ℝ)^(-3/4:ℝ)=(n:ℝ)^(1/4:ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (n:ℝ)]
    rw [← Real.rpow_add hn']
    norm_num
  calc
    _ = sourceDyadicWeight n*(n:ℝ) := by rw [hw,← he]; ring
    _ ≤ _ := by
      unfold sourceDyadicMass
      rw [sourceDyadicIndices_card,Nat.cast_add,Nat.cast_one]
      exact mul_le_mul_of_nonneg_left (by linarith) (sourceDyadicWeight_nonneg n)

theorem sourceDyadic_radius_eventually (A : ℝ) :
    ∀ᶠn : ℕ in atTop,A ≤ (2:ℝ)^n :=
  (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<2 by norm_num)).eventually_ge_atTop A

theorem sourceDyadic_scale_bounds {n i : ℕ} (hi : i∈sourceDyadicIndices n) :
    1 ≤ (2:ℝ)^i ∧ (2:ℝ)^i ≤ sourceDyadicN n ∧
      (2:ℝ)^i/sourceDyadicN n ≤ (1/4:ℝ)^n := by
  obtain ⟨hi₀,hi₁⟩ := Finset.mem_Icc.mp hi
  have hp := pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) hi₁
  have hN : sourceDyadicN n=((2:ℝ)^(2*n))^2 := by
    unfold sourceDyadicN; rw [← pow_mul]; congr 1; omega
  have h4 : (4:ℝ)^n=(2:ℝ)^(2*n) := by rw [pow_mul]; norm_num
  refine ⟨one_le_pow₀ (by norm_num),?_,?_⟩
  · unfold sourceDyadicN
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · calc
      _ ≤ (2:ℝ)^(2*n)/sourceDyadicN n := div_le_div_of_nonneg_right hp (sourceDyadicN_pos n).le
      _ = _ := by rw [hN,div_pow,one_pow,h4]; field_simp

end SourceSignalScales

section WeightedResolvent
open Classical Matrix

theorem finiteL2Norm_sum {ι α : Type*} [Fintype ι] (I : Finset α) (f : α → ι → ℝ) :
    finiteL2Norm (∑i∈I,f i) ≤ ∑i∈I,finiteL2Norm (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [finiteL2Norm]
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (finiteL2Norm_add _ _).trans (add_le_add le_rfl ih)

theorem finite_weighted_resolvent {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset α) (M : α → Matrix ι ι ℝ) (hM : ∀i∈I,(M i).PosSemidef)
    {w E : ℝ} (hw : 0 ≤ w) (hE : 0 ≤ E) (h : ι → ℝ)
    (he : ∀i∈I,finiteL2Norm (M i*ᵥh-h) ≤ E) :
    let B := w • ∑i∈I,M i
    let W := w*(I.card:ℝ)
    finiteL2Norm ((1+B)⁻¹*ᵥh) ≤ finiteL2Norm h/(1+W)+E := by
  dsimp only
  let B := w • ∑i∈I,M i
  let W := w*(I.card:ℝ)
  have hB : B.PosSemidef := (Matrix.posSemidef_sum I hM).smul hw
  have hW : 0 ≤ W := mul_nonneg hw (Nat.cast_nonneg _)
  have herr : B*ᵥh-W • h = w • ∑i∈I,(M i*ᵥh-h) := by
    simp only [B,W,Matrix.smul_mulVec,Matrix.sum_mulVec,Finset.sum_sub_distrib,
      Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,smul_sub,smul_smul]
  have hb : finiteL2Norm (B*ᵥh-W • h) ≤ W*E := by
    rw [herr,finiteL2Norm_smul,abs_of_nonneg hw]
    calc
      _ ≤ w*(∑i∈I,finiteL2Norm (M i*ᵥh-h)) := mul_le_mul_of_nonneg_left (finiteL2Norm_sum _ _) hw
      _ ≤ w*(∑_i∈I,E) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum he) hw
      _ = _ := by simp [W,mul_assoc]
  change finiteL2Norm ((1+B)⁻¹*ᵥh) ≤ finiteL2Norm h/(1+W)+E
  have hi := finiteL2Norm_inverse_signal B hB W hW h
  refine hi.trans ?_
  rw [add_div]
  apply add_le_add le_rfl
  apply (div_le_iff₀ (show 0<1+W by linarith)).mpr
  exact hb.trans (by nlinarith)

end WeightedResolvent

section FiniteSupportEnergy
open Classical Matrix

theorem finite_support_error_energy {ι : Type*} (J T : Finset ι) (hJT : J⊆T)
    (M : Matrix ι ι ℝ) (h : ι → ℝ)
    (hcol : ∀x y,y∉J → M x y*h y=0)
    (e : ι → ℝ) (he : ∀x,e x=(∑y∈J,M x y*h y)-h x)
    (hesupp : ∀x,x∉J → e x=0) :
    finiteL2Norm ((fun (x y : T) => M x y)*ᵥ(fun x : T => h x)-(fun x : T => h x))^2=
      ∑x∈J,(e x)^2 := by
  have hsum (x : ι) : (∑y : T,M x y*h y)=∑y∈J,M x y*h y := by
    rw [Finset.sum_coe_sort T (fun y => M x y*h y)]
    exact (Finset.sum_subset hJT (fun y _ hy => hcol x y hy)).symm
  have herr (x : T) : (((fun (x y : T) => M x y)*ᵥ(fun x : T => h x))-
      (fun x : T => h x)) x=e x := by
    simp only [Pi.sub_apply,Matrix.mulVec,dotProduct,hsum,he]
  rw [finiteL2Norm_sq]
  simp_rw [herr]
  rw [Finset.sum_coe_sort T (fun x => (e x)^2)]
  exact (Finset.sum_subset hJT (fun x _ hx => by rw [hesupp x hx]; norm_num)).symm

theorem finiteL2Norm_le_of_energy {ι : Type*} [Fintype ι] {x : ι → ℝ} {A B c d : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hc : 0≤c) (hd : 0≤d)
    (he : finiteL2Norm x^2 ≤ A*c^2+B*d^2) :
    finiteL2Norm x ≤ Real.sqrt A*c+Real.sqrt B*d := by
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have hnon : 0≤Real.sqrt A*c+Real.sqrt B*d := by positivity
  apply (sq_le_sq₀ (finiteL2Norm_nonneg _) hnon).mp
  refine he.trans ?_
  nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg A) hc) (mul_nonneg (Real.sqrt_nonneg B) hd)]

end FiniteSupportEnergy

end SimpleAmenable
end
end

end OAI
