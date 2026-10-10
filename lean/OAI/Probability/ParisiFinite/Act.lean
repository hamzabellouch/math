import Mathlib
import OAI.Probability.ParisiFinite.WComm

namespace OAI

/-! Act. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped BigOperators
namespace ProbeProduct
variable {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def act (T : ι → H →L[ℂ] H) : List ι → H →L[ℂ] H
  | [] => ContinuousLinearMap.id ℂ H
  | j::l => (T j).comp (act T l)

@[simp] theorem act_nil (T : ι → H →L[ℂ] H) (x : H) : act T [] x=x := rfl
@[simp] theorem act_cons (T : ι → H →L[ℂ] H) (j : ι) (l : List ι) (x : H) :
    act T (j::l) x=T j (act T l x) := rfl

theorem norm_act_le (T : ι → H →L[ℂ] H) (l : List ι)
    (hT : ∀ j ∈ l, ∀ x, ‖T j x‖ ≤ ‖x‖) (x : H) : ‖act T l x‖ ≤ ‖x‖ := by
  induction l with
  | nil => simp
  | cons j l ih =>
    exact (hT j (by simp) _).trans (ih (fun k hk => hT k (by simp [hk])))

 

theorem firstOrder_remainder (T : ι → H →L[ℂ] H) (y : ι → H) (x : H)
    (r a b : ℝ) (l : List ι) (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hT : ∀ j ∈ l, ∀ z, ‖T j z‖ ≤ ‖z‖)
    (hfirst : ∀ j ∈ l, ‖T j x-x-r • y j‖ ≤ a)
    (hcross : ∀ j ∈ l, ∀ k ∈ l, ‖T j (y k)-y k‖ ≤ b) :
    ‖act T l x-x-r • (l.map y).sum‖ ≤ l.length*a+l.length^2*|r| *b := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hTl : ∀ k ∈ l, ∀ z, ‖T k z‖ ≤ ‖z‖ := fun k hk => hT k (by simp [hk])
    have hfl : ∀ k ∈ l, ‖T k x-x-r • y k‖ ≤ a := fun k hk => hfirst k (by simp [hk])
    have hcl : ∀ k ∈ l, ∀ k' ∈ l, ‖T k (y k')-y k'‖ ≤ b :=
      fun k hk k' hk' => hcross k (by simp [hk]) k' (by simp [hk'])
    have hj := hfirst j (by simp)
    have hi := ih hTl hfl hcl
    have hc : ‖T j (l.map y).sum-(l.map y).sum‖ ≤ l.length*b := by
      have hs : T j (l.map y).sum-(l.map y).sum =
          (l.map (fun k => T j (y k)-y k)).sum := by
        have hh : ∀ l : List ι, T j (l.map y).sum-(l.map y).sum =
            (l.map (fun k => T j (y k)-y k)).sum := by
          intro ll
          induction ll with
          | nil => simp
          | cons k ll ihh =>
            simp only [List.map_cons,List.sum_cons,map_add]
            rw [← ihh]
            abel
        exact hh l
      rw [hs]
      calc
        _ ≤ ((l.map (fun k => T j (y k)-y k)).map norm).sum := by
          have hh : ∀ xs : List H, ‖xs.sum‖ ≤ (xs.map norm).sum := by
            intro xs
            induction xs with
            | nil => simp
            | cons z xs ihh =>
              simpa only [List.sum_cons,List.map_cons] using
                (norm_add_le z xs.sum).trans (add_le_add_right ihh ‖z‖)
          exact hh _
        _ ≤ (l.map (fun _ => b)).sum := by
          rw [List.map_map]
          exact List.sum_le_sum (fun k hk => hcross j (by simp) k (by simp [hk]))
        _ = _ := by simp
    have he : act T (j::l) x-x-r • ((j::l).map y).sum =
        T j (act T l x-x-r • (l.map y).sum) +
        (T j x-x-r • y j) + r • (T j (l.map y).sum-(l.map y).sum) := by
      simp only [act_cons,map_sub,ContinuousLinearMap.map_smul_of_tower,
        List.map_cons,List.sum_cons,smul_add,smul_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖T j (act T l x-x-r • (l.map y).sum)‖+
          ‖T j x-x-r • y j‖+‖r • (T j (l.map y).sum-(l.map y).sum)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ (l.length*a+l.length^2*|r| *b)+a+|r| *(l.length*b) := by
        gcongr
        · exact (hT j (by simp) _).trans hi
        · simpa only [norm_smul,Real.norm_eq_abs] using
            mul_le_mul_of_nonneg_left hc (abs_nonneg r)
      _ ≤ _ := by
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        have hn : (0:ℝ) ≤ l.length := Nat.cast_nonneg _
        have hrb : 0 ≤ |r| *b := mul_nonneg (abs_nonneg r) hb
        have hnr : 0 ≤ (l.length:ℝ)* (|r| *b) := mul_nonneg hn hrb
        nlinarith

 
theorem zero_clock_remainder (T : ι → H →L[ℂ] H) (y : ι → H) (x : H)
    (r a b : ℝ) (l : List ι) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hT : ∀ j ∈ l, ∀ z, ‖T j z‖ ≤ ‖z‖)
    (hfirst : ∀ j ∈ l, ‖T j x-x-r • y j‖ ≤ a)
    (hcross : ∀ j ∈ l, ∀ k ∈ l, ‖T j (y k)-y k‖ ≤ b)
    (hclock : (l.map y).sum=0) :
    ‖act T l x-x‖ ≤ l.length*a+l.length^2*|r| *b := by
  simpa only [hclock,smul_zero,sub_zero] using
    firstOrder_remainder T y x r a b l ha hb hT hfirst hcross

 
theorem error_of_norm_remainder (T : ι → H →L[ℂ] H) (l : List ι)
    (hT : ∀ j ∈ l, ∀ z, ‖T j z‖ ≤ ‖z‖) (x ρ : H) :
    ‖act T l (x+ρ)-(x+ρ)‖ ≤ ‖act T l x-x‖+2*‖ρ‖ := by
  have he : act T l (x+ρ)-(x+ρ)=(act T l x-x)+(act T l ρ-ρ) := by
    rw [map_add]
    abel
  rw [he]
  have hh := norm_sub_le (act T l ρ) ρ
  have hn := norm_act_le T l hT ρ
  have ht := norm_add_le (act T l x-x) (act T l ρ-ρ)
  linarith

end ProbeProduct

namespace CoherentFock
open Complex
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem matrixMass_nonneg (A : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ matrixMass A :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

 

theorem scaled_probe_error (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (r : ℝ) (v w : E) (x : PreSpin E) :
    ‖probe A (r • v) (spinCoe x)-spinCoe x-r • (I • probeField A w x)‖ ≤
      (r^2*‖v‖^2+|r| *‖v-w‖)*matrixMass A*spinBound x := by
  have he : probe A (r • v) (spinCoe x)-spinCoe x-r • (I • probeField A w x) =
      (probe A (r • v) (spinCoe x)-spinCoe x-I • probeField A (r • v) x)+
      r • (I • probeField A (v-w) x) := by
    rw [probeField_real_smul,probeField_sub,smul_sub,smul_sub,smul_comm I r]
    abel
  rw [he]
  calc
    _ ≤ ‖probe A (r • v) (spinCoe x)-spinCoe x-I • probeField A (r • v) x‖+
        ‖r • (I • probeField A (v-w) x)‖ := norm_add_le _ _
    _ ≤ ‖r • v‖^2*matrixMass A*spinBound x+
        |r| *(‖v-w‖*matrixMass A*spinBound x) := by
      apply add_le_add (probe_taylor A hA (r • v) x)
      simp only [norm_smul,Complex.norm_I,one_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_probeField_le A hA (v-w) x) (abs_nonneg r)
    _ = _ := by
      simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      ring

 

theorem zero_clock_spin_probes {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (v w : ι → E)
    (r L M Δ : ℝ) (x : PreSpin E)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hΔ : 0 ≤ Δ)
    (hA : ∀ j ∈ l, A j ∈ unitary _)
    (hv : ∀ j ∈ l, ‖v j‖ ≤ L) (hw : ∀ j ∈ l, ‖w j‖ ≤ L)
    (hd : ∀ j ∈ l, ‖v j-w j‖ ≤ Δ)
    (hMass : ∀ j ∈ l, matrixMass (A j) ≤ M)
    (hMassStar : ∀ j ∈ l, matrixMass (A j).conjTranspose ≤ M)
    (hclock : (l.map fun j => I • probeField (A j) (w j) x).sum=0) :
    ‖ProbeProduct.act (fun j => probe (A j) (r • v j)) l (spinCoe x)-spinCoe x‖ ≤
      l.length*((r^2*L^2+|r| *Δ)*M*spinBound x)+
        l.length^2*|r| *(2*|r| *L^2*M^3*spinBound x) := by
  have hS := spinBound_nonneg x
  apply ProbeProduct.zero_clock_remainder
    (fun j => probe (A j) (r • v j)) (fun j => I • probeField (A j) (w j) x)
    (spinCoe x) r ((r^2*L^2+|r| *Δ)*M*spinBound x) (2*|r| *L^2*M^3*spinBound x) l
  · positivity
  · positivity
  · intro j hj z
    exact (norm_probe (A j) (hA j hj) (r • v j) z).le
  · intro j hj
    exact (scaled_probe_error (A j) (hA j hj) r (v j) (w j) x).trans (by
      gcongr
      · exact matrixMass_nonneg _
      · exact hv j hj
      · exact hd j hj
      · exact hMass j hj)
  · intro j hj k hk
    simp only [map_smul,← smul_sub,norm_smul,Complex.norm_I,one_mul]
    have hb := probe_cross (A j) (A k) (hA j hj) (r • v j) (w k) x
    simp only [norm_smul,Real.norm_eq_abs] at hb
    calc
      _ ≤ 2*(|r| *‖v j‖)*‖w k‖*matrixMass (A j)*matrixMass (A k).conjTranspose*
          matrixMass (A k)*spinBound x := hb
      _ ≤ 2*(|r| *L)*L*M*M*M*spinBound x := by
        gcongr
        · exact matrixMass_nonneg _
        · exact matrixMass_nonneg _
        · exact matrixMass_nonneg _
        · exact hv j hj
        · exact hw k hk
        · exact hMass j hj
        · exact hMassStar k hk
        · exact hMass k hk
      _ = _ := by ring
  · exact hclock

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

def mass (x : PreSpace E) : ℝ := (toFinsupp x).sum (fun _ a => ‖a‖)

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem mass_nonneg (x : PreSpace E) : 0 ≤ mass x := by
  classical
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

 

def RadiusLE (x : PreSpace E) (B : ℝ) : Prop :=
  ∀ e ∈ (toFinsupp x).support, ‖e‖ ≤ B

theorem translated_coherent_bound (d e x y : E) (s : ℝ) (hs : 0 ≤ s)
    (hsep : s+‖x‖+‖y‖ ≤ ‖d-e‖) :
    ‖⟪W d (coherent x),W e (coherent y)⟫_ℂ‖ ≤ Real.exp (-s^2/2) := by
  rw [norm_inner_translated_coherent]
  apply Real.exp_le_exp.mpr
  have ht := norm_sub_norm_le (d-e) (-(x-y))
  simp only [norm_neg,sub_neg_eq_add] at ht
  have hxy := norm_sub_le x y
  have heq : d-e+(x-y)=(d+x)-(e+y) := by abel
  rw [heq] at ht
  have hlow : s ≤ ‖(d+x)-(e+y)‖ := by linarith
  nlinarith [norm_nonneg ((d+x)-(e+y))]

 

theorem translated_pre_bound (d e : E) (x y : PreSpace E) (B s : ℝ)
    (hx : RadiusLE x B) (hy : RadiusLE y B) (hs : 0 ≤ s)
    (hsep : s+2*B ≤ ‖d-e‖) :
    ‖⟪W d (↑x),W e (↑y)⟫_ℂ‖ ≤ mass x*mass y*Real.exp (-s^2/2) := by
  classical
  simp_rw [coe_eq_sum,Finsupp.sum,map_sum,map_smul,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right]
  calc
    _ ≤ ∑ a ∈ (toFinsupp x).support, ∑ b ∈ (toFinsupp y).support,
        ‖conj ((toFinsupp x) a)*((toFinsupp y) b*⟪W d (coherent a),W e (coherent b)⟫_ℂ)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => norm_sum_le _ _)
    _ ≤ ∑ a ∈ (toFinsupp x).support, ∑ b ∈ (toFinsupp y).support,
        ‖(toFinsupp x) a‖*(‖(toFinsupp y) b‖*Real.exp (-s^2/2)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      simp only [norm_mul,Complex.norm_conj]
      gcongr
      exact translated_coherent_bound d e a b s hs (by linarith [hx a ha,hy b hb])
    _ = _ := by
      simp only [mass,Finsupp.sum,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm (s := (toFinsupp y).support)]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

 
theorem scaled_translated_pre_bound (d e : E) (x y : PreSpace E) (B δ R : ℝ)
    (hx : RadiusLE x B) (hy : RadiusLE y B) (hδ : 0 < δ)
    (hsep : δ ≤ ‖d-e‖) (hR : 1 ≤ R) (hB : 4*B ≤ R*δ) :
    ‖⟪W (R • d) (↑x),W (R • e) (↑y)⟫_ℂ‖ ≤
      mass x*mass y*Real.exp (-(δ^2/8)*R) := by
  have hRn : 0 ≤ R := by linarith
  have hnorm : R*δ/2+2*B ≤ ‖R • d-R • e‖ := by
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg hRn]
    nlinarith
  refine (translated_pre_bound (R • d) (R • e) x y B (R*δ/2) hx hy
    (by positivity) hnorm).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mass_nonneg x) (mass_nonneg y))
  apply Real.exp_le_exp.mpr
  have hrr : R ≤ R^2 := by nlinarith
  nlinarith [sq_nonneg δ,mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr hrr)]

 

theorem rapid_decay {α : Type*} {l : Filter α}
    (R : α → ℝ) (d e : α → E) (x y : α → PreSpace E)
    (hR : Tendsto R l atTop) (B A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hx : ∀ᶠ a in l, RadiusLE (x a) B ∧ mass (x a) ≤ A)
    (hy : ∀ᶠ a in l, RadiusLE (y a) B ∧ mass (y a) ≤ A)
    (hsep : ∀ᶠ a in l, δ ≤ ‖d a-e a‖) (M : ℕ) :
    Tendsto (fun a => (R a)^M * ‖⟪W (R a • d a) (↑(x a)),W (R a • e a) (↑(y a))⟫_ℂ‖)
      l (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ => r^M*Real.exp (-(δ^2/8)*r)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (M:ℝ) (δ^2/8) (by positivity)
  have ht' := (ht.comp hR).mul_const (A*A)
  have hr1 : ∀ᶠ a in l, 1 ≤ R a := hR.eventually (eventually_ge_atTop 1)
  have hrB : ∀ᶠ a in l, 4*B ≤ R a*δ := by
    filter_upwards [hR.eventually (eventually_ge_atTop (4*B/δ))] with a ha
    exact (div_le_iff₀ hδ).mp ha
  apply squeeze_zero' ?_ ?_ (by simpa using ht')
  · filter_upwards [hr1] with a ha
    exact mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg _)
  · filter_upwards [hr1,hrB,hx,hy,hsep] with a ha hba hxa hya hsa
    have hb := scaled_translated_pre_bound (d a) (e a) (x a) (y a) B δ (R a)
      hxa.1 hya.1 hδ hsa ha hba
    have hmass : mass (x a)*mass (y a) ≤ A*A :=
      mul_le_mul hxa.2 hya.2 (mass_nonneg _) hA
    have hb' : ‖⟪W (R a • d a) (↑(x a)),W (R a • e a) (↑(y a))⟫_ℂ‖ ≤
        A*A*Real.exp (-(δ^2/8)*R a) :=
      hb.trans (mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _))
    have hm := mul_le_mul_of_nonneg_left hb' (pow_nonneg (by linarith : 0 ≤ R a) M)
    rw [neg_mul] at hm
    nlinarith

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
@[simp] theorem mass_basis (d : E) : mass (basis d)=1 := by
  classical
  simp [mass,basis]

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
@[simp] theorem mass_zero : mass (0 : PreSpace E)=0 := by simp [mass]

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem mass_add_le (x y : PreSpace E) : mass (x+y) ≤ mass x+mass y := by
  convert! WeightedMass.add_le (fun _ : E => (1:ℝ)) (fun _ => zero_le_one)
    (toFinsupp x) (toFinsupp y) using 1 <;> simp [mass,WeightedMass.mass]

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem mass_smul (c : ℂ) (x : PreSpace E) : mass (c • x)=‖c‖*mass x := by
  convert! WeightedMass.smul (fun _ : E => (1:ℝ)) c (toFinsupp x) using 1 <;>
    simp [mass,WeightedMass.mass]

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem mass_sum {ι : Type*} (s : Finset ι) (x : ι → PreSpace E) :
    mass (∑ i ∈ s, x i) ≤ ∑ i ∈ s, mass (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (mass_add_le _ _).trans (add_le_add_right ih _)

omit [InnerProductSpace ℂ E] in
theorem RadiusLE.zero (B : ℝ) : RadiusLE (0 : PreSpace E) B := by simp [RadiusLE]

omit [InnerProductSpace ℂ E] in
theorem RadiusLE.basis (d : E) (B : ℝ) (hd : ‖d‖ ≤ B) : RadiusLE (basis d) B := by
  classical
  simpa [RadiusLE,CoherentFock.basis] using hd

omit [InnerProductSpace ℂ E] in
theorem RadiusLE.add {x y : PreSpace E} {B : ℝ} (hx : RadiusLE x B) (hy : RadiusLE y B) :
    RadiusLE (x+y) B := by
  classical
  intro d hd
  rw [map_add] at hd
  rcases Finset.mem_union.mp (Finsupp.support_add hd) with h|h
  · exact hx d h
  · exact hy d h

omit [InnerProductSpace ℂ E] in
theorem RadiusLE.smul {x : PreSpace E} {B : ℝ} (hx : RadiusLE x B) (c : ℂ) :
    RadiusLE (c • x) B := by
  intro d hd
  rw [map_smul] at hd
  exact hx d (Finsupp.support_smul hd)

omit [InnerProductSpace ℂ E] in
theorem RadiusLE.sum {ι : Type*} (s : Finset ι) (x : ι → PreSpace E) (B : ℝ)
    (hx : ∀ i ∈ s, RadiusLE (x i) B) : RadiusLE (∑ i ∈ s, x i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RadiusLE.zero B
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hx i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

omit [InnerProductSpace ℂ E] in
theorem RadiusLE.mono {x : PreSpace E} {B C : ℝ} (hx : RadiusLE x B) (hBC : B ≤ C) :
    RadiusLE x C := fun d hd => (hx d hd).trans hBC

theorem mass_preW_le (d : E) (x : PreSpace E) : mass (preWLinear d x) ≤ mass x := by
  classical
  conv_lhs => rw [← sum_basis x]
  simp only [Finsupp.sum,map_sum]
  calc
    _ ≤ ∑ e ∈ (toFinsupp x).support, mass (preWLinear d ((toFinsupp x) e • basis e)) :=
      mass_sum _ _
    _ = mass x := by
      simp only [map_smul,preWLinear_basis,mass_smul,mass_basis,norm_phase,mul_one]
      rfl

theorem RadiusLE.preW {x : PreSpace E} {B : ℝ} (hx : RadiusLE x B) (d : E) :
    RadiusLE (preWLinear d x) (‖d‖+B) := by
  classical
  rw [← sum_basis x]
  simp only [Finsupp.sum,map_sum]
  apply RadiusLE.sum
  intro e he
  rw [map_smul,preWLinear_basis]
  exact ((RadiusLE.basis (d+e) _ ((norm_add_le _ _).trans (add_le_add_right (hx e he) _))).smul _).smul _

omit [InnerProductSpace ℂ E] in
theorem secondTailBound_le_mass (x : PreSpace E) {B : ℝ} (_hB : 0 ≤ B) (hx : RadiusLE x B) :
    secondTailBound x ≤ mass x*(1+2*B+12*B^2) := by
  classical
  simp only [secondTailBound,mass,Finsupp.sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  gcongr <;> exact hx d hd

 

theorem finite_packet_displacement (d : E) (x : PreSpace E) {B C : ℝ}
    (hx : RadiusLE x B) (hd : ‖d‖ ≤ C) :
    (↑(preWLinear d x) : Space E)=W d (↑x) ∧
      mass (preWLinear d x) ≤ mass x ∧ RadiusLE (preWLinear d x) (C+B) := by
  exact ⟨(W_coe d x).symm,mass_preW_le d x,(hx.preW d).mono (by linarith)⟩

end CoherentFock

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace ℂ E']

theorem mass_preGamma_le (T : E →ₗᵢ[ℂ] E') (x : PreSpace E) :
    mass (preGammaLinear T x) ≤ mass x := by
  classical
  conv_lhs => rw [← sum_basis x]
  simp only [Finsupp.sum,map_sum]
  calc
    _ ≤ ∑ e ∈ (toFinsupp x).support, mass (preGammaLinear T ((toFinsupp x) e • basis e)) :=
      mass_sum _ _
    _ = mass x := by
      simp only [map_smul,preGammaLinear_basis,mass_smul,mass_basis,mul_one]
      rfl

theorem RadiusLE.preGamma {x : PreSpace E} {B : ℝ} (hx : RadiusLE x B) (T : E →ₗᵢ[ℂ] E') :
    RadiusLE (preGammaLinear T x) B := by
  classical
  rw [← sum_basis x]
  simp only [Finsupp.sum,map_sum]
  apply RadiusLE.sum
  intro e he
  rw [map_smul,preGammaLinear_basis]
  exact (RadiusLE.basis (T e) _ (by simpa using hx e he)).smul _

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
def spinMass (x : PreSpin E) : ℝ := ∑ i, mass (x i)

def SpinRadiusLE (x : PreSpin E) (B : ℝ) : Prop := ∀ i, RadiusLE (x i) B

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem spinMass_nonneg (x : PreSpin E) : 0 ≤ spinMass x :=
  Finset.sum_nonneg (fun i _ => mass_nonneg (x i))

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem mass_le_spinMass (x : PreSpin E) (i : Fin 2) : mass (x i) ≤ spinMass x :=
  Finset.single_le_sum (fun j _ => mass_nonneg (x j)) (Finset.mem_univ i)

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
theorem spinMass_preRoot (A : Matrix (Fin 2) (Fin 2) ℂ) (x : PreSpin E) :
    spinMass (preRoot A x) ≤ matrixMass A*spinMass x := by
  classical
  unfold spinMass preRoot
  calc
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖*mass (x j) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mass_smul] using mass_sum Finset.univ (fun j => A i j • x j)
    _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖A i j‖*spinMass x := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (mass_le_spinMass x j) (norm_nonneg _)
    _ = _ := by simp only [matrixMass,Finset.sum_mul,spinMass]

omit [InnerProductSpace ℂ E] in
theorem SpinRadiusLE.preRoot {x : PreSpin E} {B : ℝ} (hx : SpinRadiusLE x B)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : SpinRadiusLE (preRoot A x) B := by
  intro i
  exact RadiusLE.sum Finset.univ (fun j => A i j • x j) B (fun j _ => (hx j).smul _)

omit [InnerProductSpace ℂ E] in
theorem spinBound_le_mass (x : PreSpin E) {B : ℝ} (hB : 0 ≤ B) (hx : SpinRadiusLE x B) :
    spinBound x ≤ spinMass x*(1+2*B+12*B^2) := by
  unfold spinBound spinMass
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => secondTailBound_le_mass (x i) hB (hx i))

def preWZ (d : E) (x : PreSpin E) : PreSpin E :=
  fun i => preWLinear (if i=0 then d else -d) (x i)

@[simp] theorem spinCoe_preWZ (d : E) (x : PreSpin E) : spinCoe (preWZ d x)=WZ d (spinCoe x) := by
  ext i
  simp only [spinCoe_apply,preWZ,WZ_apply,W_coe]

theorem spinMass_preWZ (d : E) (x : PreSpin E) : spinMass (preWZ d x) ≤ spinMass x :=
  Finset.sum_le_sum (fun i _ => mass_preW_le _ (x i))

theorem SpinRadiusLE.preWZ {x : PreSpin E} {B : ℝ} (hx : SpinRadiusLE x B) (d : E) :
    SpinRadiusLE (preWZ d x) (‖d‖+B) := by
  intro i
  change RadiusLE (preWLinear (if i=0 then d else -d) (x i)) (‖d‖+B)
  split_ifs
  · exact (hx i).preW d
  · simpa only [norm_neg] using (hx i).preW (-d)

 
def preProbe (A : Matrix (Fin 2) (Fin 2) ℂ) (d : E) (x : PreSpin E) : PreSpin E :=
  preRoot A.conjTranspose (preWZ d (preRoot A x))

@[simp] theorem spinCoe_preProbe (A : Matrix (Fin 2) (Fin 2) ℂ) (d : E) (x : PreSpin E) :
    spinCoe (preProbe A d x)=probe A d (spinCoe x) := by
  simp only [preProbe,spinCoe_preRoot,spinCoe_preWZ,probe_apply]

theorem spinMass_preProbe (A : Matrix (Fin 2) (Fin 2) ℂ) (d : E) (x : PreSpin E) :
    spinMass (preProbe A d x) ≤ matrixMass A.conjTranspose*matrixMass A*spinMass x := by
  apply (spinMass_preRoot _ _).trans
  calc
    _ ≤ matrixMass A.conjTranspose*spinMass (preRoot A x) :=
      mul_le_mul_of_nonneg_left (spinMass_preWZ _ _) (matrixMass_nonneg _)
    _ ≤ matrixMass A.conjTranspose*(matrixMass A*spinMass x) :=
      mul_le_mul_of_nonneg_left (spinMass_preRoot _ _) (matrixMass_nonneg _)
    _ = _ := by ring

theorem SpinRadiusLE.preProbe {x : PreSpin E} {B : ℝ} (hx : SpinRadiusLE x B)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (d : E) : SpinRadiusLE (preProbe A d x) (‖d‖+B) :=
  ((hx.preRoot A).preWZ d).preRoot A.conjTranspose

end CoherentFock

namespace ProbeProduct
variable {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

 

theorem perturbation_bound (T S : ι → H →L[ℂ] H) (l : List ι) (ε : ℝ)
    (hε : 0 ≤ ε) (hT : ∀ j ∈ l, ∀x, ‖T j x‖ ≤ ‖x‖)
    (hS : ∀ j ∈ l, ∀x, ‖S j x‖ ≤ ‖x‖)
    (hE : ∀ j ∈ l, ∀x, ‖T j x-S j x‖ ≤ ε*‖x‖) (x : H) :
    ‖act T l x-act S l x‖ ≤ l.length*ε*‖x‖ := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hTl : ∀ k ∈ l, ∀z, ‖T k z‖ ≤ ‖z‖ := fun k hk => hT k (by simp [hk])
    have hSl : ∀ k ∈ l, ∀z, ‖S k z‖ ≤ ‖z‖ := fun k hk => hS k (by simp [hk])
    have hEl : ∀ k ∈ l, ∀z, ‖T k z-S k z‖ ≤ ε*‖z‖ := fun k hk => hE k (by simp [hk])
    have hi := ih hTl hSl hEl
    have he : act T (j::l) x-act S (j::l) x =
        T j (act T l x-act S l x)+(T j (act S l x)-S j (act S l x)) := by
      simp only [act_cons,map_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖T j (act T l x-act S l x)‖+‖T j (act S l x)-S j (act S l x)‖ := norm_add_le _ _
      _ ≤ l.length*ε*‖x‖+ε*‖act S l x‖ :=
        add_le_add ((hT j (by simp) _).trans hi) (hE j (by simp) _)
      _ ≤ l.length*ε*‖x‖+ε*‖x‖ := by
        gcongr
        exact norm_act_le S l hSl x
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

end ProbeProduct

namespace CoherentFock
open Complex
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 
def spinW (d : E) : SpinSpace E →L[ℂ] SpinSpace E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => Space E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (W d).comp (PiLp.proj 2 (fun _ : Fin 2 => Space E) i))

@[simp] theorem spinW_apply (d : E) (x : SpinSpace E) (i : Fin 2) : spinW d x i=W d (x i) := rfl

@[simp] theorem norm_spinW (d : E) (x : SpinSpace E) : ‖spinW d x‖=‖x‖ := by
  have hh : ‖spinW d x‖^2=‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    simp
  nlinarith [norm_nonneg x,norm_nonneg (spinW d x)]

theorem spinW_root (d : E) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : SpinSpace E) :
    spinW d (SpinOperators.act A x)=SpinOperators.act A (spinW d x) := by
  ext i
  simp only [spinW_apply,SpinOperators.act_apply,map_sum,map_smul]

def phaseZ (θ : ℝ) : SpinSpace E →L[ℂ] SpinSpace E :=
  SpinOperators.act (Matrix.diagonal fun i : Fin 2 =>
    Complex.exp (((if i=0 then θ else -θ : ℝ):ℂ)*I))

@[simp] theorem phaseZ_apply (θ : ℝ) (x : SpinSpace E) (i : Fin 2) :
    phaseZ θ x i=Complex.exp (((if i=0 then θ else -θ : ℝ):ℂ)*I) • x i := by
  simp [phaseZ,SpinOperators.act_apply,Matrix.diagonal_apply]

@[simp] theorem norm_phaseZ (θ : ℝ) (x : SpinSpace E) : ‖phaseZ θ x‖=‖x‖ := by
  have hh : ‖phaseZ θ x‖^2=‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    simp only [phaseZ_apply,norm_smul,Complex.norm_exp_ofReal_mul_I,one_mul]
  nlinarith [norm_nonneg x,norm_nonneg (phaseZ θ x)]

theorem phaseZ_sub_le (θ : ℝ) (x : SpinSpace E) : ‖phaseZ θ x-x‖ ≤ |θ| *‖x‖ := by
  have hc (i : Fin 2) : ‖(phaseZ θ x-x) i‖ ≤ |θ| *‖x i‖ := by
    simp only [PiLp.sub_apply,phaseZ_apply]
    have he : Complex.exp (((if i=0 then θ else -θ : ℝ):ℂ)*I) • x i-x i =
        (Complex.exp (((if i=0 then θ else -θ : ℝ):ℂ)*I)-1) • x i := by
      rw [sub_smul,one_smul]
    rw [he,norm_smul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    split_ifs
    · simpa only [mul_comm,Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
    · simpa only [mul_comm,Real.norm_eq_abs,abs_neg] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := -θ)
  have hh : ‖phaseZ θ x-x‖^2 ≤ (|θ| *‖x‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,PiLp.norm_sq_eq_of_L2,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have := hc i
    nlinarith [norm_nonneg ((phaseZ θ x-x) i),norm_nonneg (x i),abs_nonneg θ]
  nlinarith [norm_nonneg (phaseZ θ x-x),mul_nonneg (abs_nonneg θ) (norm_nonneg x)]

 

theorem centered_WZ (d e : E) (x : SpinSpace E) :
    spinW (-e) (WZ d (spinW e x))=phaseZ (-2*(⟪d,e⟫_ℂ).im) (WZ d x) := by
  ext i
  simp only [spinW_apply,WZ_apply,phaseZ_apply]
  split_ifs with hi
  · exact congrArg (fun T : Space E →L[ℂ] Space E => T (x i)) (centered_probe d e)
  · simpa only [inner_neg_left,Complex.neg_im,mul_neg,neg_mul,neg_neg,
      ContinuousLinearMap.comp_apply,smul_apply]
      using congrArg (fun T : Space E →L[ℂ] Space E => T (x i)) (centered_probe (-d) e)

 
def probePhase (A : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) : SpinSpace E →L[ℂ] SpinSpace E :=
  (SpinOperators.act A.conjTranspose).comp ((phaseZ θ).comp (SpinOperators.act A))

@[simp] theorem probePhase_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (x : SpinSpace E) :
    probePhase A θ x=SpinOperators.act A.conjTranspose (phaseZ θ (SpinOperators.act A x)) := rfl

@[simp] theorem norm_probePhase (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) (θ : ℝ)
    (x : SpinSpace E) : ‖probePhase A θ x‖=‖x‖ := by
  rw [probePhase_apply,SpinOperators.norm_act (root_adjoint_unitary A hA),norm_phaseZ,SpinOperators.norm_act hA]

theorem probePhase_sub_le (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) (θ : ℝ)
    (x : SpinSpace E) : ‖probePhase A θ x-x‖ ≤ |θ| *‖x‖ := by
  have he : probePhase A θ x-x=SpinOperators.act A.conjTranspose
      (phaseZ θ (SpinOperators.act A x)-SpinOperators.act A x) := by
    rw [map_sub,root_left_inverse A hA]
    rfl
  rw [he,SpinOperators.norm_act (root_adjoint_unitary A hA)]
  simpa only [SpinOperators.norm_act hA] using phaseZ_sub_le θ (SpinOperators.act A x)

theorem root_right_inverse (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (x : SpinSpace E) : SpinOperators.act A (SpinOperators.act A.conjTranspose x)=x := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    root_left_inverse A.conjTranspose (root_adjoint_unitary A hA) x

 
theorem centered_toggled_probe (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _)
    (d e : E) (x : SpinSpace E) :
    spinW (-e) (probe A d (spinW e x))=
      probePhase A (-2*(⟪d,e⟫_ℂ).im) (probe A d x) := by
  rw [probe_apply,spinW_root,← spinW_root e A x,centered_WZ]
  simp only [probePhase_apply,probe_apply,root_right_inverse A hA]

end CoherentFock

end

end OAI
