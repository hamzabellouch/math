import Mathlib
import OAI.Probability.LogConcave.Sampling.NormalizedScoreMajorant

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma physicalBase_envelope {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (q j : ℕ) (y : Point d) :
    spatialEnvelope (TensorExpression.physicalBase F x r ρ ((lam:ℝ)*r) q) j y≤
      (2:ℝ)^(j+q+2)*normalizedTensorMajorant (j+q+2) (1-ρ^2) := by
  unfold spatialEnvelope spatialTensor TensorExpression.physicalBase
  have hh := normalizedTensor_spatial_allSplit hF x hr hlam hl hρ0 hρ1 y
    (fun i : Fin (q+2) => decide (i=Fin.last (q+1))) (List.finRange (q+2)) (by simp)
    (List.nodup_finRange _) (by simp) (List.finRange j) (List.nodup_finRange _) (by simp)
  have hb := TensorEnergy.splitEnvelope_le_pow (normalizedTensorMajorant_nonneg _ _) hh
  simpa only [Fintype.card_sum,
    Fintype.card_fin,Nat.add_assoc] using hb

lemma physicalBase_envelope_budget {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (q j n : ℕ) (y : Point d) :
    ENNReal.ofReal (spatialEnvelope (TensorExpression.physicalBase F x r ρ ((lam:ℝ)*r) q) j y)≤
      (((100*(q+3):ℕ):ℝ≥0∞)*ENNReal.ofReal (analyticBase d j n))^((100*(q+3))*(j+1))*
        ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)^(q+j) := by
  let C := 100*(q+3)
  let b := analyticBase d j n
  let D : ℝ := (C:ℝ)*b
  let R := (Real.sqrt (1-ρ^2))⁻¹
  have hb : 1≤b := analyticBase_one_le _ _ _
  have hb' : (j:ℝ)+1≤b := (analyticBase_nat_le d j n).2
  have hD2 : 2≤D := by dsimp [D,C]; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q]
  have hD : 1≤D := by linarith
  have hR0 : 0≤R := by dsimp [R]; positivity
  have ha : 0<1-ρ^2 := (probability_time hρ0 hρ1).1
  have hMb : 10*(((j+q+2:ℕ):ℝ)+1)≤D := by
    dsimp [D,C]; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) q,Nat.cast_nonneg (α:=ℝ) j]
  have hp : spatialEnvelope (TensorExpression.physicalBase F x r ρ ((lam:ℝ)*r) q) j y≤
      D^(C*(j+1))*R^(q+j) := by
    calc
      _ ≤ (2:ℝ)^(j+q+2)*normalizedTensorMajorant (j+q+2) (1-ρ^2) := physicalBase_envelope hF x hr hlam hl hρ0 hρ1 q j y
      _ ≤ (2:ℝ)^(j+q+2)*((10*(((j+q+2:ℕ):ℝ)+1))^(4*(j+q+2+1))*R^(j+q+2-2)) :=
        mul_le_mul_of_nonneg_left (normalizedTensorMajorant_le ha _) (by positivity)
      _ ≤ D^(j+q+2)*(D^(4*(j+q+3))*R^(q+j)) := by
        rw [show j+q+2-2=q+j by omega,show j+q+2+1=j+q+3 by omega]
        exact mul_le_mul (pow_le_pow_left₀ (by norm_num) hD2 _) (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hMb _) (pow_nonneg hR0 _)) (by positivity) (by positivity)
      _ = D^(j+q+2+4*(j+q+3))*R^(q+j) := by rw [pow_add]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hR0 _)
        apply pow_le_pow_right₀ hD
        dsimp [C]
        nlinarith only [Nat.zero_le (q*j),Nat.zero_le q,Nat.zero_le j]
  have hh := ENNReal.ofReal_le_ofReal hp
  simpa only [ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one hD) _),
    ENNReal.ofReal_pow (le_trans zero_le_one hD),ENNReal.ofReal_pow hR0,
    D,ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast] using hh

theorem physicalBase_tame {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] (q : ℕ) :
    TameAt μ (TensorExpression.physicalBase F x r ρ ((lam:ℝ)*r) q)
      q (100*(q+3)) (ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)) := by
  intro j n _
  apply (lintegral_mono (fun y => pow_le_pow_left' (physicalBase_envelope_budget hF x hr hlam hl hρ0 hρ1 q j n y) n)).trans
  simp only [lintegral_const,measure_univ,mul_one,le_refl]

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

def finSnocSlots (m : ℕ) : Fin (m+1) ≃ Fin m ⊕ Unit :=
  finSumFinEquiv.symm.trans ((Equiv.refl (Fin m)).sumCongr finOneEquiv)

lemma finSnocSlots_castSucc (m : ℕ) (i : Fin m) : finSnocSlots m i.castSucc=Sum.inl i := by
  simp [finSnocSlots]

lemma finSnocSlots_last (m : ℕ) : finSnocSlots m (Fin.last m)=Sum.inr () := by
  simp [finSnocSlots,finOneEquiv]

lemma snoc_through_slots {m d : ℕ} (c : Fin m → Fin d) (z : Fin d) :
    (Sum.elim c (fun _ : Unit => z)) ∘ finSnocSlots m=Fin.snoc c z := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Function.comp_apply,finSnocSlots_last,Sum.elim_inr,Fin.snoc_last]
  · simp only [Function.comp_apply,finSnocSlots_castSucc,Sum.elim_inl,Fin.snoc_castSucc]

namespace TensorExpression

def profileConstant {n : ℕ} : TensorExpression n → ℕ
  | .jet q => 100*(q+3)
  | .perm _ A => 4*(A.profileConstant+n+1)
  | .contract (m:=m) (n:=n) _ _ A B =>
      4*(4*(4*(A.profileConstant+m+2)+4*(B.profileConstant+n+2)+m+n+1)+m+n+1)
  | .adjoint (n:=n) _ A => adjointConstant (4*(A.profileConstant+n+2)) n

lemma profileConstant_ge {n : ℕ} (A : TensorExpression n) : 20≤A.profileConstant := by
  induction A with
  | jet q => dsimp [profileConstant]; omega
  | perm e A ih => dsimp [profileConstant]; omega
  | contract hm hn A B ihA ihB => dsimp [profileConstant]; omega
  | adjoint hn A ih =>
    dsimp [profileConstant]
    exact (by norm_num : 20≤120).trans (adjointConstant_bounds (by omega)).2.2.2.2

theorem eval_tame {d : ℕ} {base : ∀q : ℕ,(Fin (q+2) → Fin d) → Point d → ℝ}
    {H : Point d → ℝ} {K : ℝ≥0} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hK : LipschitzWith K (gradient H)) [IsProbabilityMeasure (gibbs H)]
    (hbase : ∀q c,PolySmooth (base q c)) {R : ℝ≥0∞}
    (hR : 1≤R) (hRf : R≠⊤) (hscore : TameScore H R) (hd : 1≤d)
    (hb : ∀q,TameAt (gibbs H) (base q) q (100*(q+3)) R)
    {n : ℕ} (A : TensorExpression n) :
    TameAt (gibbs H) (A.eval base H) A.weight A.profileConstant R := by
  induction A with
  | jet q => exact hb q
  | perm e A ih =>
    simp only [eval,weight,profileConstant]
    simpa only [Fintype.card_fin] using TameAt.reindex (gibbs H) (A.eval base H) (eval_polySmooth hbase hH A) e A.profileConstant_ge ih
  | @contract m n hm hn A B ihA ihB =>
    let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    let FA := fun a : Fin m ⊕ Unit → Fin d => A.eval base H (a ∘ finSnocSlots m)
    let FB := fun a : Fin n ⊕ Unit → Fin d => B.eval base H (a ∘ finSnocSlots n)
    have hFA : ∀c,PolySmooth (FA c) := fun c => eval_polySmooth hbase hH A _
    have hFB : ∀c,PolySmooth (FB c) := fun c => eval_polySmooth hbase hH B _
    have hta : TameAt (gibbs H) FA A.weight (4*(A.profileConstant+m+2)) R := by
      simpa only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,Nat.add_assoc] using
        TameAt.reindex (gibbs H) (A.eval base H) (eval_polySmooth hbase hH A) (finSnocSlots m) A.profileConstant_ge ihA
    have htb : TameAt (gibbs H) FB B.weight (4*(B.profileConstant+n+2)) R := by
      simpa only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,Nat.add_assoc] using
        TameAt.reindex (gibbs H) (B.eval base H) (eval_polySmooth hbase hH B) (finSnocSlots n) B.profileConstant_ge ihB
    have hc := TameAt.contract (gibbs H) FA FB hFA hFB
      (by have := A.profileConstant_ge; omega) (by have := B.profileConstant_ge; omega) hta htb
    have hFc (a : Fin m ⊕ Fin n → Fin d) : PolySmooth
        (fun y => TensorEnergy.singleContract (fun c => FA c y) (fun c => FB c y) a) := by
      exact PolySmooth.sum Finset.univ (fun z _ => (hFA _).mul (hFB _))
    have hh := TameAt.reindex (gibbs H) _ hFc finSumFinEquiv
      (by simp only [Fintype.card_fin]; omega) hc
    have he : (fun a y => TensorEnergy.singleContract (fun c => FA c y) (fun c => FB c y) (a ∘ finSumFinEquiv))=
        (TensorExpression.contract hm hn A B).eval base H := by
      funext a y
      unfold TensorEnergy.singleContract TensorExpression.eval
      apply Finset.sum_congr rfl
      intro z _
      dsimp [FA,FB]
      rw [snoc_through_slots,snoc_through_slots]
    rw [he] at hh
    simpa only [profileConstant,weight,Fintype.card_fin,Nat.add_assoc] using hh
  | @adjoint n hn A ih =>
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
    let FA := fun a : Fin n ⊕ Unit → Fin d => A.eval base H (a ∘ finSnocSlots n)
    have hFA : ∀c,PolySmooth (FA c) := fun c => eval_polySmooth hbase hH A _
    have hta : TameAt (gibbs H) FA A.weight (4*(A.profileConstant+n+2)) R := by
      simpa only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,Nat.add_assoc] using
        TameAt.reindex (gibbs H) (A.eval base H) (eval_polySmooth hbase hH A) (finSnocSlots n) A.profileConstant_ge ih
    have hh := TameAt.adjoint hH ht hK FA hFA hd (by have := A.profileConstant_ge; omega) hR hRf hscore hta
    have he : (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
        (fun z => FA (Sum.elim a (fun _ => z))))=(TensorExpression.adjoint hn A).eval base H := by
      funext a
      dsimp [FA,TensorExpression.eval]
      simp only [snoc_through_slots]
    rw [he] at hh
    simpa only [profileConstant,weight,Fintype.card_fin] using hh

end TensorExpression
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

lemma physicalScale_one_le {ρ : ℝ} (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    1≤ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹) := by
  have ha := (probability_time hρ0 hρ1).1
  have hs : 0<Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr ha
  have hu : Real.sqrt (1-ρ^2)≤1 := (Real.sqrt_le_one).mpr (by nlinarith [sq_nonneg ρ])
  exact_mod_cast ENNReal.ofReal_le_ofReal (one_le_inv₀ hs |>.mpr hu)

theorem TensorExpression.physical_tame {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hd : 1≤d) {n : ℕ} (A : TensorExpression n) :
    TameAt (interpolationLaw F x r ρ)
      (A.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ))
      A.weight A.profileConstant (ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)) := by
  have hlt : (lam:ℝ)*r^2<1 := by linarith
  have hp : ρ^2<1 := by have := (probability_time hρ0 hρ1).1; linarith
  have he := interpolationLaw_eq_gibbs hF x hr.le hlt hp
  let : IsProbabilityMeasure (interpolationLaw F x r ρ) := interpolationLaw_probability hF x hr.le hlt ρ
  let : IsProbabilityMeasure (gibbs (interpolationPotential F x r ρ)) := he ▸ inferInstance
  rw [he]
  exact A.eval_tame (interpolationPotential_polySmooth hF x hr hlam hl hρ0 hρ1)
    (interpolationPotential_lowerTail hF x hr.le hlt hρ0 hρ1)
    (interpolationPotential_gradient_lipschitz hF x hr.le hl hρ0 hρ1)
    (physicalBase_polySmooth hF x hr hlam hl hρ0 hρ1)
    (physicalScale_one_le hρ0 hρ1) ENNReal.ofReal_ne_top
    (physicalTameScore hF x hr hlam hl hρ0 hρ1) hd
    (physicalBase_tame hF x hr hlam hl hρ0 hρ1 _)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal Matrix.Norms.L2Operator

lemma TameAt.eLpNorm {S : Type} [Fintype S] {d : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {F : (S → Fin d) → Point d → ℝ}
    (hF : ∀c,PolySmooth (F c)) {k C : ℕ} {R : ℝ≥0∞}
    (h : TameAt μ F k C R) (j : ℕ) {p : ℝ≥0∞} (hpf : p≠⊤) :
    eLpNorm (spatialEnvelope F j) p μ≤
      ((4*(C:ℝ≥0∞))*ENNReal.ofReal (p.toReal+j+Real.log ((d:ℝ)+1)+1))^(C*(j+1))*R^(k+j) := by
  let n := Nat.ceil p.toReal+2
  have hp : p≤(n:ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal hpf (ENNReal.natCast_ne_top n)).mp
    simp only [ENNReal.toReal_natCast]
    have hh := Nat.le_ceil p.toReal
    dsimp [n]
    push_cast
    linarith
  have hm : AEStronglyMeasurable (spatialEnvelope F j) μ :=
    (TensorEnergy.measurable_splitEnvelope _ (fun c =>
      ((hF _).jet _ _).smooth.continuous.measurable)).aestronglyMeasurable
  apply (eLpNorm_le_eLpNorm_of_exponent_le (μ:=μ) (f:=spatialEnvelope F j) hp).trans
  have hnorm := eLpNorm_nnreal_eq_eLpNorm' (p:=(n:ℝ≥0))
    (by exact_mod_cast (show n ≠ 0 by omega)) hm
  simp only [ENNReal.coe_natCast,NNReal.coe_natCast] at hnorm
  rw [hnorm]
  apply ((norm_le_iff_natural_moment (μ:=μ) (spatialEnvelope_nonneg F j) (by omega : 0<n) _).mpr (h j n (by omega))).trans
  apply mul_le_mul' _ le_rfl
  apply pow_le_pow_left'
  have hb : analyticBase d j n≤4*(p.toReal+j+Real.log ((d:ℝ)+1)+1) := by
    have hceil' : (Nat.ceil p.toReal:ℝ)≤p.toReal+1 := (Nat.ceil_lt_add_one (ENNReal.toReal_nonneg)).le
    have hlog := Real.log_nonneg (show (1:ℝ)≤(d:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) d])
    dsimp [analyticBase,n]
    push_cast
    linarith [ENNReal.toReal_nonneg (a:=p),Nat.cast_nonneg (α:=ℝ) j]
  have hh := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),ENNReal.ofReal_ofNat] at hh
  convert mul_le_mul' (le_refl (C:ℝ≥0∞)) hh using 1; ring

theorem TensorExpression.physical_split_Lp {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (hd : 1≤d) {n : ℕ} (A : TensorExpression n) (j : ℕ)
    (e : TensorEnergy.ProperSplit (Fin j ⊕ Fin n)) {p : ℝ≥0∞} (hpf : p≠⊤) :
    eLpNorm (fun y => TensorEnergy.splitMatrix
      (spatialTensor (A.eval (physicalBase F x r ρ ((lam:ℝ)*r))
        (interpolationPotential F x r ρ)) (List.finRange j) y) e) p (interpolationLaw F x r ρ)≤
      ((4*(A.profileConstant:ℝ≥0∞))*ENNReal.ofReal (p.toReal+j+Real.log ((d:ℝ)+1)+1))^(A.profileConstant*(j+1))*
        ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)^(A.weight+j) := by
  let : IsProbabilityMeasure (interpolationLaw F x r ρ) := interpolationLaw_probability hF x hr.le (by linarith) ρ
  have hpoly := eval_polySmooth (physicalBase_polySmooth hF x hr hlam hl hρ0 hρ1)
    (interpolationPotential_polySmooth hF x hr hlam hl hρ0 hρ1) A
  apply (eLpNorm_mono_real
    (continuous_matrix (fun _ _ => ((hpoly _).jet _ _).smooth.continuous)).aestronglyMeasurable
    (fun y => TensorEnergy.splitMatrix_norm_le _ e)).trans
  exact TameAt.eLpNorm hpoly
    (A.physical_tame hF x hr hlam hl hρ0 hρ1 hd) j hpf

end LogConcaveSampling

end

end

end

end OAI
