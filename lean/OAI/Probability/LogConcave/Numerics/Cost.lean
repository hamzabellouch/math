import Mathlib
import OAI.Probability.LogConcave.Numerics.RowGaussian

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def cost : MeanTree X d → ℕ
  | .node _ _ _ _ _ C => ∑i,(1+cost (C i))

@[simp] lemma cost_anchor (b : X → Point d) (hb : Measurable b) : cost (anchor b hb)=0 := by simp [cost,anchor]
@[simp] lemma cost_zero : cost (zero : MeanTree X d)=0 := by simp [zero]
@[simp] lemma cost_scale (s : ℝ) (E : MeanTree X d) : cost (scale s E)=cost E := by cases E; rfl
@[simp] lemma cost_add (E D : MeanTree X d) : cost (add E D)=cost E+cost D := by
  cases E; cases D
  simp only [cost,add,Fin.sum_univ_add,Fin.addCases_left,Fin.addCases_right]
@[simp] lemma cost_mean (r : ℝ) (E : MeanTree X d) : cost (mean r E)=1+cost E := by simp [cost,mean]
@[simp] lemma cost_conditional (r ρ : ℝ) (E D : MeanTree X d) : cost (conditional r ρ E D)=1+cost E+cost D := by
  simp [conditional,Nat.add_assoc]
@[simp] lemma cost_sumFin (k : ℕ) (E : Fin k → MeanTree X d) : cost (sumFin k E)=∑i,cost (E i) := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => simp [sumFin,ih,Fin.sum_univ_succ]
@[simp] lemma cost_sumFamily {I : Type*} [Fintype I] (E : I → MeanTree X d) :
    cost (sumFamily E)=∑i,cost (E i) := by
  rw [sumFamily,cost_sumFin]
  exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

theorem compileDeclared_size (D A : ℝ) (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (S Q : ℕ) (hM : ∀r τ,P r τ → (M r τ).slots≤S ∧ (M r τ).calls≤Q)
    (E : MeanTree X d) (n : ℝ) (hready : ShiftReady D A P E n) :
    (compileDeclared D A M E n).slots≤1+cost E*(S+1) ∧
      (compileDeclared D A M E n).calls≤cost E*Q := by
  induction E generalizing n with | node k b hb a r C ih =>
    have hc (i) := ih i (r i/(2*D)) (hready i).2.2
    have hm (i) := hM (r i) (declaredNoise n A) (hready i).2.1
    constructor
    · simp only [compileDeclared,slots_compileTerms,Expression.slots,cost]
      apply Nat.add_le_add_left
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h₁ := (hc i).1
      have h₂ := (hm i).1
      nlinarith
    · simp only [calls_compileDeclared,cost,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      have h₁ := (hc i).2
      have h₂ := (hm i).2
      nlinarith

def DriftBound (R : ℝ) : (E : MeanTree X d) → DriftData E → Prop
  | .node _ _ _ _ r C,p => ∀i,|((p.2 i).root (C i))/(r i)|≤R ∧ DriftBound R (C i) (p.2 i)

theorem compileDeclaredShift_energy_bound {D A R B : ℝ} (hD : 0<D) (_hR : 0≤R) (hB : 0≤B)
    (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (hv : ∀r τ,P r τ → (∑j,(M r τ).shift j^2)≤D^2)
    (hBv : ∀r τ,P r τ → (∑j,(M r τ).shift j^2)≤B)
    (E : MeanTree X d) (n : ℝ) (p : DriftData E)
    (hready : ShiftReady D A P E n) (hg : DriftBound R E p) :
    (∑j,compileDeclaredShift D A M E n p j^2)≤(cost E:ℝ)*(4*R^2*B) := by
  induction E generalizing n with | node k b hb a r C ih =>
    change (∑j,compileTermsShift D k a (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) (.noise b hb (declaredReserve n A a))
      (fun i => compileDeclaredShift D A M (C i) (r i/(2*D)) (p.2 i))
      (fun i => inverseChildShift D (r i) ((p.2 i).root (C i)) (M (r i) (declaredNoise n A)))
      (fun _ => 0) j^2)≤_
    rw [compileTermsShift_energy]
    simp only [zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero,zero_add,cost,Nat.cast_sum,Nat.cast_add,Nat.cast_one,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hc := ih i (r i/(2*D)) (p.2 i) (hready i).2.2 (hg i).2
    have hi := inverse_shift_energy (fun j => (M (r i) (declaredNoise n A)).shift j/(2*D))
      (M (r i) (declaredNoise n A)).shift (normalized_shift_bound hD _ (hv _ _ (hready i).2.1))
      (((p.2 i).root (C i))/(r i))
    have hs := hBv _ _ (hready i).2.1
    have hh : (((p.2 i).root (C i))/(r i))^2≤R^2 := by
      have hb := pow_le_pow_left₀ (abs_nonneg _) (hg i).1 2
      simpa only [sq_abs] using hb
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤4)) hB
    have hv' := mul_le_mul_of_nonneg_left hs (show 0≤4*(((p.2 i).root (C i))/(r i))^2 by positivity)
    change (∑j,compileDeclaredShift D A M (C i) (r i/(2*D)) (p.2 i) j^2)+
      (∑j,inverseChildShift D (r i) ((p.2 i).root (C i)) (M (r i) (declaredNoise n A)) j^2)≤_
    change (∑j,inverseChildShift D (r i) ((p.2 i).root (C i)) (M (r i) (declaredNoise n A)) j^2)≤_ at hi
    nlinarith
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma sqrt_one_sub_sq_gap {ρ : ℝ} (hρ : ρ∈Icc (0:ℝ) 1) :
    1-ρ≤Real.sqrt (1-ρ^2) := by
  have hp : 0≤1-ρ^2 := by nlinarith [hρ.1,hρ.2]
  have hs := Real.sq_sqrt hp
  nlinarith [Real.sqrt_nonneg (1-ρ^2),hρ.1,hρ.2]

lemma mean_direct_ratio {ρ T θ : ℝ} (hT : 1/2≤T) (hT1 : T<1)
    (hρ : ρ∈Icc (0:ℝ) T) (hθ : θ^2≤Real.sqrt (1-T^2)) :
    0<Real.sqrt (1-ρ^2) ∧ |(1-ρ*Real.cos θ/T)/Real.sqrt (1-ρ^2)|≤3 := by
  have hT0 : 0<T := by linarith
  have hρ1 : ρ<1 := hρ.2.trans_lt hT1
  have hp : 0<1-ρ^2 := by nlinarith [hρ.1]
  have hs : 0<Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr hp
  have hc := Real.one_sub_sq_div_two_le_cos (x:=θ)
  have hcos := Real.cos_le_one θ
  have hn : 0≤1-ρ*Real.cos θ/T := by
    rw [sub_nonneg,div_le_iff₀ hT0,one_mul]
    exact (mul_le_mul_of_nonneg_left hcos hρ.1).trans (by simpa using hρ.2)
  have hτ := sqrt_one_sub_sq_gap ⟨hρ.1,hρ1.le⟩
  have hθ' : θ^2≤Real.sqrt (1-ρ^2) := hθ.trans (Real.sqrt_le_sqrt (by nlinarith [hρ.1,hρ.2]))
  have hr : ρ*Real.cos θ≥ρ*(1-θ^2/2) := mul_le_mul_of_nonneg_left hc hρ.1
  have hd : (1-ρ*Real.cos θ/T)≤3*Real.sqrt (1-ρ^2) := by
    have hm₁ := mul_le_mul_of_nonneg_left hθ' hρ.1
    have hm₂ := mul_le_mul_of_nonneg_right hρ.2 (Real.sqrt_nonneg (1-ρ^2))
    have hm₃ := mul_le_mul_of_nonneg_right hT (Real.sqrt_nonneg (1-ρ^2))
    have hnum : T-ρ*Real.cos θ≤3*Real.sqrt (1-ρ^2)*T := by nlinarith
    calc
      1-ρ*Real.cos θ/T=(T-ρ*Real.cos θ)/T := by rw [sub_div,div_self hT0.ne']
      _≤3*Real.sqrt (1-ρ^2) := (div_le_iff₀ hT0).mpr hnum
  refine ⟨hs,?_⟩
  rw [abs_of_nonneg (div_nonneg hn hs.le),div_le_iff₀ hs]
  exact hd

lemma sample_direct_ratio {ρ T : ℝ} (_hT : 0≤T) (hT1 : T<1) (hρ : ρ∈Icc (0:ℝ) T) :
    0<Real.sqrt (1-ρ^2) ∧ |(1-ρ*T)/Real.sqrt (1-ρ^2)|≤2 := by
  have hρ1 : ρ<1 := hρ.2.trans_lt hT1
  have hp : 0<1-ρ^2 := by nlinarith [hρ.1]
  have hs : 0<Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr hp
  have hn : 0≤1-ρ*T := by nlinarith [hρ.1,mul_nonneg hρ.1 (sub_nonneg.mpr hT1.le)]
  have hτ := sqrt_one_sub_sq_gap ⟨hρ.1,hρ1.le⟩
  refine ⟨hs,?_⟩
  rw [abs_of_nonneg (div_nonneg hn hs.le),div_le_iff₀ hs]
  nlinarith [mul_nonneg hρ.1 (sub_nonneg.mpr hρ.2),sq_nonneg (1-ρ)]

theorem exists_driftData (f : Point d → X → X) (R : ℝ) (E : MeanTree X d) (c : ℝ)
    (hc : ∀Δ z,base E (f Δ z)=base E z+c • Δ)
    (hE : centers (fun r b => ∃c : ℝ,(∀Δ z,b (f Δ z)=b z+c • Δ) ∧ |c/r|≤R) E) :
    ∃p : DriftData E,DriftValid f E p ∧ p.root E=c ∧ DriftBound R E p := by
  induction E generalizing c with | node k b hb a r C ih =>
    choose c' hshift hratio using fun i => (hE i).1
    have hh (i : Fin k) := ih i (c' i) (hshift i) (hE i).2
    choose p hp hroot hbound using hh
    exact ⟨(c,p),⟨hc,hp⟩,rfl,fun i => ⟨by simpa only [hroot i] using hratio i,hbound i⟩⟩

omit [MeasurableSpace X] in
lemma DirectCenter.shift {r T v α r' : ℝ} {x Y G b : X → Point d}
    (f : Point d → X → X)
    (hx : ∀Δ z,x (f Δ z)=x z+r • Δ)
    (hY : ∀Δ z,Y (f Δ z)=Y z-α • Δ)
    (hG : ∀Δ z,G (f Δ z)=G z)
    (hb : DirectCenter r T v x Y G r' b) :
    ∃ρ∈Icc (0:ℝ) T,∃θ,|θ|≤v ∧ r'=r*Real.sqrt (1-ρ^2) ∧
      ∀Δ z,b (f Δ z)=b z+(r*(1-ρ*Real.cos θ*α)) • Δ := by
  obtain ⟨ρ,hρ,θ,hθ,hr,hb⟩ := hb
  refine ⟨ρ,hρ,θ,hθ,hr,?_⟩
  intro Δ z
  rw [hb]
  simp only [hx,hY,hG,oriented,smul_add,smul_sub,smul_smul]
  module

omit [MeasurableSpace X] in
lemma DirectCenter.mean_shift {r T v r' : ℝ} (hr : 0<r) (hT : 1/2≤T) (hT1 : T<1)
    (hv : v^2≤Real.sqrt (1-T^2)) {x Y G b : X → Point d}
    (f : Point d → X → X)
    (hx : ∀Δ z,x (f Δ z)=x z+r • Δ)
    (hY : ∀Δ z,Y (f Δ z)=Y z-T⁻¹ • Δ)
    (hG : ∀Δ z,G (f Δ z)=G z)
    (hb : DirectCenter r T v x Y G r' b) :
    0<r' ∧ ∃c : ℝ,(∀Δ z,b (f Δ z)=b z+c • Δ) ∧ |c/r'|≤3 := by
  obtain ⟨ρ,hρ,θ,hθ,hr',hshift⟩ := hb.shift f hx hY hG
  have hθ' : θ^2≤Real.sqrt (1-T^2) := by
    have hpow := pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    simp only [sq_abs] at hpow
    exact hpow.trans hv
  obtain ⟨hτ,hbound⟩ := mean_direct_ratio hT hT1 hρ hθ'
  refine ⟨hr' ▸ mul_pos hr hτ,r*(1-ρ*Real.cos θ*T⁻¹),hshift,?_⟩
  rw [hr',mul_div_mul_left _ _ hr.ne']
  simpa only [div_eq_mul_inv] using hbound
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {d : ℕ}

abbrev MeanInput (d : ℕ) := Point d × (Point d × Point d)
abbrev SampleInput (d : ℕ) := Point d × Point d

def meanInputMove (r T : ℝ) (Δ : Point d) (z : MeanInput d) : MeanInput d :=
  (z.1+r • Δ,(z.2.1-T⁻¹ • Δ,z.2.2))
def sampleInputMove (r T : ℝ) (Δ : Point d) (z : SampleInput d) : SampleInput d :=
  (z.1+r • Δ,z.2-T • Δ)

def literalMean (r T h ψ σ : ℝ) (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1)) :
    MeanTree (MeanInput d) d :=
  meanCircuit r T h ψ (σ/2) n m N nc Nc e
    (anchor Prod.fst (by fun_prop)) (anchor (fun z => z.2.1) (by fun_prop))
    (anchor (fun z => z.2.2) (by fun_prop))

def literalSample (r T h : ℝ) (n N : ℕ) (e : ProbabilityNode T h n) :
    MeanTree (SampleInput d) d :=
  scale T⁻¹ (forward r T h n N (anchor Prod.fst (by fun_prop))
    (anchor Prod.snd (by fun_prop)) e)

lemma literalMean_geometry {r T h ψ σ v : ℝ} {n m N nc Nc : ℕ}
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v) (e : ProbabilityNode T h (n+1)) :
    base (literalMean (d:=d) r T h ψ σ n m N nc Nc e)=(fun z => (σ/2) • z.2.2) ∧
    centers (DirectCenter r T v Prod.fst (fun z : MeanInput d => z.2.1) (fun z => z.2.2))
      (literalMean r T h ψ σ n m N nc Nc e) := by
  exact meanCircuit_centers_direct hT hT1 hh hv _ _ _ rfl rfl rfl hψ
    (centers_anchor _ _ _) (centers_anchor _ _ _) (centers_anchor _ _ _) e

lemma literalSample_geometry {r T h : ℝ} {n N : ℕ} (hn : 0<n)
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (e : ProbabilityNode T h n) :
    base (literalSample (d:=d) r T h n N e)=(fun z => T⁻¹ • z.2) ∧
    centers (DirectCenter r T 0 Prod.fst Prod.snd (fun _ : SampleInput d => 0))
      (literalSample r T h n N e) := by
  have hg := forward_centers_direct (r:=r) (N:=N) (v:=0) (θ:=0) (x:=Prod.fst) (Y:=Prod.snd) (G:=fun _ : SampleInput d => 0) hn hT hT1 hh
    (anchor (Prod.fst : SampleInput d → Point d) (by fun_prop)) (anchor Prod.snd (by fun_prop))
    rfl (by simp only [base_anchor,oriented_zero]) (by norm_num) (centers_anchor _ _ _) (centers_anchor _ _ _) e
  exact ⟨by simp only [literalSample,base_scale,hg.1,base_anchor],
    (centers_scale _ _ _).2 hg.2⟩

theorem literalMean_drift {r T h ψ σ v : ℝ} {n m N nc Nc : ℕ}
    (hr : 0<r) (hT : 1/2≤T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    (hvsmall : v^2≤Real.sqrt (1-T^2))
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v) (e : ProbabilityNode T h (n+1)) :
    ∃p : DriftData (literalMean (d:=d) r T h ψ σ n m N nc Nc e),
      DriftValid (meanInputMove r T) _ p ∧ p.root _=0 ∧ DriftBound 3 _ p := by
  have hg := literalMean_geometry (d:=d) (r:=r) (σ:=σ) (N:=N) (nc:=nc) (Nc:=Nc)
    (by linarith : 0<T) hT1 hh hv hψ e
  apply exists_driftData (meanInputMove r T) 3 _ 0
  · intro Δ z
    rw [hg.1]
    simp [meanInputMove]
  · apply centers_mono _ (fun r' b hb => ?_) hg.2
    exact (hb.mean_shift hr hT hT1 hvsmall (meanInputMove r T)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)).2

theorem literalSample_drift {r T h : ℝ} {n N : ℕ}
    (hr : 0<r) (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    (e : ProbabilityNode T h n) :
    ∃p : DriftData (literalSample (d:=d) r T h n N e),
      DriftValid (sampleInputMove r T) _ p ∧ p.root _ = -1 ∧ DriftBound 2 _ p := by
  have hg := literalSample_geometry (d:=d) (r:=r) (N:=N) hn hT hT1 hh e
  apply exists_driftData (sampleInputMove r T) 2 _ (-1)
  · intro Δ z
    rw [hg.1]
    simp only [sampleInputMove,smul_sub,smul_smul,inv_mul_cancel₀ hT.ne',one_smul,neg_one_smul]
    rfl
  · apply centers_mono _ (fun r' b hb => ?_) hg.2
    obtain ⟨ρ,hρ,θ,hθ,hr',hshift⟩ := hb.shift (sampleInputMove r T)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    have hθ0 : θ=0 := abs_nonpos_iff.mp hθ
    refine ⟨r*(1-ρ*T),?_,?_⟩
    · simpa only [hθ0,Real.cos_zero,mul_one] using hshift
    · rw [hr',mul_div_mul_left _ _ hr.ne']
      exact (sample_direct_ratio hT.le hT1 hρ).2
end LogConcaveSampling.MeanTree

end

end

end OAI
