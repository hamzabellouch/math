import Mathlib
import OAI.Probability.LogConcave.Sampling.NaturalMomentNorm
import OAI.Probability.LogConcave.Sampling.SpatialTensor
import OAI.Probability.LogConcave.Sampling.ScoreAugmented
import OAI.Probability.LogConcave.TensorGraphs.FieldPosition

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.L2Operator

lemma natural_moment_root_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : ∀x,0≤f x) {n a j k : ℕ} (hn : 0<n)
    (C D A R : ℝ≥0∞)
    (h : (∫⁻x,ENNReal.ofReal (f x)^n ∂μ) ≤
      C^n*D^a*(A^(2*n*(j+1))*R^(n*(k+j+1)))) :
    eLpNorm' f (n:ℝ) μ ≤
      C*D^((a:ℝ)/(n:ℝ))*A^(2*(j+1))*R^(k+j+1) := by
  apply (norm_le_iff_natural_moment (μ:=μ) hf hn _).mpr
  convert h using 1
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hD : (D^((a:ℝ)/(n:ℝ)))^n=D^a := by
    rw [←ENNReal.rpow_natCast,←ENNReal.rpow_mul,div_mul_cancel₀ _ hn0,
      ENNReal.rpow_natCast]
  rw [mul_pow,mul_pow,mul_pow,hD]
  simp only [←pow_mul,Nat.mul_comm,Nat.mul_left_comm,mul_assoc]

theorem adjoint_eLpNorm {s a b d : ℕ} {H : Point d → ℝ} (v : Fin d → Point d)
    (F : (Fin a ⊕ Fin b → Fin d) → Fin d → Point d → ℝ)
    (ha : 0<a) (hb : 0<b) {K : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hK : LipschitzWith K (gradient H))
    (hF : ∀c z,PolySmooth (F c z))
    (M N : ℕ → Point d → ℝ)
    (hM0 : ∀e x,0≤M e x) (hN0 : ∀e x,0≤N e x)
    (hM : ∀e x,TensorEnergy.AllSplitBound (CycleTrace.fieldPosition v F e x) (M e x))
    (hN : ∀e x,TensorEnergy.AllSplitBound (CycleTrace.scorePosition H v e x) (N e x))
    (j k : ℕ) (A R : ℝ≥0∞) (hA : 1≤A) (hR : 1≤R) (hAf : A≠⊤) (hRf : R≠⊤)
    (hMm : ∀e,AEMeasurable (fun x => ENNReal.ofReal (M e x)) (gibbs H))
    (hp : ∀e≤2*(s+1),(∫⁻x,ENNReal.ofReal (M e x)^(2*(s+1)) ∂gibbs H) ≤
      (A^(j+e+1)*R^(k+j+e))^(2*(s+1)))
    (hh : ∀e≤2*(s+1),∀x,ENNReal.ofReal (N e x)≤A^(e+1)*R^e) :
    eLpNorm (fun x => ‖CycleTrace.adjointMatrix H v F x‖) (2*(s+1):ℝ≥0∞) (gibbs H) ≤
      (3*(2*(s+1))+1)*(d:ℝ≥0∞)^((a:ℝ)/(2*(s+1):ℝ))*
        A^(2*(j+1))*R^(k+j+1) := by
  have hcont : Continuous (CycleTrace.adjointMatrix H v F) :=
    continuous_matrix fun _ _ => (hH.tensorAdjoint (fun z => hF _ z) v).smooth.continuous
  have hnorm := eLpNorm_nnreal_eq_eLpNorm' (μ:=gibbs H)
    (p:=((2*(s+1):ℕ):ℝ≥0)) (by positivity) hcont.norm.aestronglyMeasurable
  push_cast at hnorm
  rw [hnorm]
  have h := CycleTrace.adjoint_trace_moment v F ha hb hH ht hK hF M N hM0 hN0 hM hN
    j k A R hA hR hAf hRf hMm hp hh
  have he : 2*s+2=2*(s+1) := by omega
  simpa only [he,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using
    natural_moment_root_product (gibbs H) (fun x => ‖CycleTrace.adjointMatrix H v F x‖)
      (fun _ => norm_nonneg _) (by omega : 0<2*(s+1))
      ((3*(2*s+2)+1:ℕ):ℝ≥0∞) (d:ℝ≥0∞) A R (by simpa only [he] using h)

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal RealInnerProductSpace

lemma scoreAugmented_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {K : Type} [Fintype K] (l : List K) (hlN : l.Nodup) (hall : ∀k,k∈l) (y : Point d) :
    TensorEnergy.AllSplitBound (scoreAugmented (interpolationPotential F x r ρ) l y)
      ((if l=[] then 1 else 0)+normalizedTensorMajorant (Fintype.card K+2) (1-ρ^2)) := by
  let k : List (K ⊕ Unit) := l.map Sum.inl++[Sum.inr ()]
  have hkN : k.Nodup := by
    simpa using JetCalculus.nodup_sum_append hlN (by simp : ([()] : List Unit).Nodup)
  have hkall : ∀t : K ⊕ Unit,t∈k := by intro t; cases t <;> simp [k,hall]
  have hkkN : (k.map Sum.inl++[Sum.inr ()]).Nodup := by
    simpa using JetCalculus.nodup_sum_append hkN (by simp : ([()] : List Unit).Nodup)
  have hkkall : ∀t : (K ⊕ Unit) ⊕ Unit,t∈k.map Sum.inl++[Sum.inr ()] := by
    intro t; cases t <;> simp [hkall]
  let C := (r*ρ)*(ρ^(Fintype.card K+1)*((lam:ℝ)*r))
  have hC0 : 0≤C := by dsimp [C]; positivity
  have hC1 : C≤1 := by
    have he : C=((lam:ℝ)*r^2)*ρ^(Fintype.card K+2) := by dsimp [C]; rw [pow_succ]; ring
    rw [he]
    have hh := mul_le_of_le_one_right (show (0:ℝ)≤(lam:ℝ)*r^2 by positivity)
      (pow_le_one₀ (n:=Fintype.card K+2) hρ0 hρ1.le)
    linarith
  have hm0 := normalizedTensorMajorant_nonneg (Fintype.card K+2) (1-ρ^2)
  have hN := (normalizedTensor_allSplit hF x hr hlam hl hρ0 hρ1 y
    (Sum.elim (fun _ : K ⊕ Unit => false) (fun _ : Unit => true))
    (k.map Sum.inl++[Sum.inr ()]) hkkN hkkall).const_mul C
  simp only [Fintype.card_sum,Fintype.card_unique,Nat.add_assoc] at hN
  have hNm := hN.mono (mul_nonneg hC0 hm0) (mul_le_of_le_one_left hm0 hC1)
  have hD := TensorEnergy.allSplitBound_spatial_delta (d:=d) l hall
  have he := hD.add hNm (by split_ifs <;> norm_num) hm0
  convert he using 1
  funext c
  exact scoreAugmented_eq hF x hr hlam hl hρ0 hρ1 l (list_length_full l hlN hall) y c

def scoreSlots (e : ℕ) : ((Fin e ⊕ Unit) ⊕ Unit) ≃ Fin (e+2) where
  toFun := Sum.elim (Sum.elim (fun k => ⟨k.val+2,by omega⟩) (fun _ => ⟨0,by omega⟩))
    (fun _ => ⟨1,by omega⟩)
  invFun k := if h0 : k.val=0 then Sum.inl (Sum.inr ()) else
    if h1 : k.val=1 then Sum.inr () else Sum.inl (Sum.inl ⟨k.val-2,by omega⟩)
  left_inv := by
    intro t
    rcases t with (k|u)|u
    · simp only [Sum.elim_inl,Fin.val_mk,Nat.add_eq_zero_iff,OfNat.ofNat_ne_zero,and_false,
        ↓reduceDIte]
      have hn : k.val+2≠1 := by omega
      simp only [hn,↓reduceDIte,Nat.add_sub_cancel]
    · cases u; rfl
    · cases u; rfl
  right_inv := by
    intro k
    dsimp only []
    split_ifs with h0 h1
    · apply Fin.ext; exact h0.symm
    · apply Fin.ext; exact h1.symm
    · apply Fin.ext; dsimp; omega

lemma scorePosition_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (e : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound (CycleTrace.scorePosition (interpolationPotential F x r ρ)
      (EuclideanSpace.basisFun (Fin d) ℝ) e y)
      ((if e=0 then 1 else 0)+normalizedTensorMajorant (e+2) (1-ρ^2)) := by
  have hh := (scoreAugmented_allSplit hF x hr hlam hl hρ0 hρ1 (List.finRange e)
    (List.nodup_finRange e) (by simp) y).reindex (scoreSlots e)
  have he : (List.finRange e=[] ↔ e=0) := by simp
  have hf : (fun a : Fin (e+2) → Fin d => scoreAugmented (interpolationPotential F x r ρ)
      (List.finRange e) y (a ∘ scoreSlots e))=
      CycleTrace.scorePosition (interpolationPotential F x r ρ) (EuclideanSpace.basisFun (Fin d) ℝ) e y := by
    funext c
    rfl
  rw [hf] at hh
  simpa only [Fintype.card_fin,he] using hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

universe u

def contractSpatialSlots {K S T : Type u} (p : K → Prop) [DecidablePred p] :
    (({k // p k} ⊕ S) ⊕ ({k // ¬p k} ⊕ T)) ≃ K ⊕ (S ⊕ T) :=
  (Equiv.sumSumSumComm {k // p k} S {k // ¬p k} T).trans
    ((Equiv.sumCompl p).sumCongr (Equiv.refl (S ⊕ T)))

@[simp] lemma contractSpatialSlots_ll {K S T : Type u} (p : K → Prop) [DecidablePred p]
    (k : {k // p k}) : contractSpatialSlots (S:=S) (T:=T) p (Sum.inl (Sum.inl k))=Sum.inl k.val := rfl
@[simp] lemma contractSpatialSlots_lr {K S T : Type u} (p : K → Prop) [DecidablePred p]
    (s : S) : contractSpatialSlots (T:=T) p (Sum.inl (Sum.inr s))=Sum.inr (Sum.inl s) := rfl
@[simp] lemma contractSpatialSlots_rl {K S T : Type u} (p : K → Prop) [DecidablePred p]
    (k : {k // ¬p k}) : contractSpatialSlots (S:=S) (T:=T) p (Sum.inr (Sum.inl k))=Sum.inl k.val := rfl
@[simp] lemma contractSpatialSlots_rr {K S T : Type u} (p : K → Prop) [DecidablePred p]
    (t : T) : contractSpatialSlots (S:=S) p (Sum.inr (Sum.inr t))=Sum.inr (Sum.inr t) := rfl

def extendedSpatial {d : ℕ} {S K : Type u}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d)
    (c : (K ⊕ S) ⊕ Unit → Fin d) : ℝ :=
  spatialTensor F l y (c ∘ (Equiv.sumAssoc K S Unit).symm)

lemma extendedSpatial_allSplit {d : ℕ} {S K : Type u} [Fintype S] [Fintype K]
    {F : (S ⊕ Unit → Fin d) → Point d → ℝ} {l : List K} {y : Point d} {M : ℝ}
    (h : TensorEnergy.AllSplitBound (spatialTensor F l y) M) :
    TensorEnergy.AllSplitBound (extendedSpatial F l y) M :=
  h.reindex (Equiv.sumAssoc K S Unit).symm

def spatialContractTerm {d : ℕ} {S T K : Type u} (p : K → Prop) [DecidablePred p]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d)
    (c : K ⊕ (S ⊕ T) → Fin d) : ℝ :=
  TensorEnergy.singleContract (extendedSpatial F (selectList p l) y)
    (extendedSpatial G (selectList (fun k => ¬p k) l) y) (c ∘ contractSpatialSlots p)

lemma spatialContractTerm_eq {d : ℕ} {S T K : Type u} (p : K → Prop) [DecidablePred p]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d)
    (c : K ⊕ (S ⊕ T) → Fin d) :
    spatialContractTerm p F G l y c = ∑z : Fin d,
      JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k)))
        (l.filter (fun k => decide (p k))) (F (Sum.elim (fun s => c (Sum.inr (Sum.inl s))) (fun _ => z))) y *
      JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k)))
        (l.filter (fun k => decide (¬p k))) (G (Sum.elim (fun t => c (Sum.inr (Sum.inr t))) (fun _ => z))) y := by
  unfold spatialContractTerm TensorEnergy.singleContract extendedSpatial spatialTensor
  apply Finset.sum_congr rfl
  intro z _
  simp only [Function.comp_def,Equiv.sumAssoc_symm_apply_inl,Sum.elim_inl,
    contractSpatialSlots_ll,contractSpatialSlots_rl]
  rw [jet_selectList p (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k))) l,
    jet_selectList (fun k => ¬p k) (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k))) l]
  congr 2 <;> congr 1 <;> funext s <;> cases s <;> rfl

lemma spatialContractTerm_allSplit {d : ℕ} {S T K : Type u}
    [Fintype S] [Fintype T] [Fintype K] [Nonempty S] [Nonempty T]
    (p : K → Prop) [DecidablePred p]
    {F : (S ⊕ Unit → Fin d) → Point d → ℝ}
    {G : (T ⊕ Unit → Fin d) → Point d → ℝ} {l : List K} {y : Point d} {M N : ℝ}
    (hF : TensorEnergy.AllSplitBound (spatialTensor F (selectList p l) y) M)
    (hG : TensorEnergy.AllSplitBound (spatialTensor G (selectList (fun k => ¬p k) l) y) N) :
    TensorEnergy.AllSplitBound (spatialContractTerm p F G l y) (M*N) :=
  ((extendedSpatial_allSplit hF).singleContract (extendedSpatial_allSplit hG)).reindex
    (contractSpatialSlots p)

lemma spatialTensor_singleContract {d : ℕ} {S T K : Type u}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c))
    (l : List K) (hl : l.Nodup) (y : Point d) (c : K ⊕ (S ⊕ T) → Fin d) :
    spatialTensor (fun a y => TensorEnergy.singleContract (fun c => F c y) (fun c => G c y) a) l y c=
      ∑s ∈ l.toFinset.powerset,spatialContractTerm (fun k => k∈s) F G l y c := by
  unfold spatialTensor TensorEnergy.singleContract
  rw [JetCalculus.jet_sum _ (fun z _ => (hF _).mul (hG _))]
  simp_rw [JetCalculus.jet_mul (hF _) (hG _) _ l hl]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact (spatialContractTerm_eq (fun k => k∈s) F G l y c).symm

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

def spatialInside {K S : Type} {d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (c : K ⊕ S → Fin d) (z : Fin d) : Point d → ℝ :=
  JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k))) l
    (F (Sum.elim (fun s => c (Sum.inr s)) (fun _ => z)))

def spatialAdjointLeading {K S : Type} {d : ℕ}
    (H : Point d → ℝ) (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (y : Point d) (c : K ⊕ S → Fin d) : ℝ :=
  tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (spatialInside F l c) y

lemma spatialTensor_adjoint {K S : Type} {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (hl : l.Nodup) (y : Point d) (c : K ⊕ S → Fin d) :
    spatialTensor (fun a => tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun z => F (Sum.elim a (fun _ => z)))) l y c =
    spatialAdjointLeading H F l y c+
      ∑s∈l.toFinset.powerset.erase ∅,∑z : Fin d,
        JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k)))
          (l.filter (fun k => k∈s)) (directional (EuclideanSpace.basisFun (Fin d) ℝ z) H) y *
        JetCalculus.jet (fun k => EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inl k)))
          (l.filter (fun k => k∉s)) (F (Sum.elim (fun t => c (Sum.inr t)) (fun _ => z))) y := by
  exact congrFun (jet_tensorAdjoint hH.smooth (fun _ => (hF _).smooth) _ _ l hl) y

def spatialFieldSlots {K S : Type} {a b : ℕ} (h : K ⊕ S ≃ Fin a ⊕ Fin b) (e : ℕ) :
    (Fin e ⊕ K) ⊕ (S ⊕ Unit) ≃ (Fin a ⊕ Fin b) ⊕ (Unit ⊕ Fin e) :=
  (Equiv.sumAssoc (Fin e) K (S ⊕ Unit)).trans
    (((Equiv.refl (Fin e)).sumCongr (Equiv.sumAssoc K S Unit).symm).trans
      ((Equiv.sumComm (Fin e) ((K ⊕ S) ⊕ Unit)).trans
        ((Equiv.sumAssoc (K ⊕ S) Unit (Fin e)).trans (h.sumCongr (Equiv.refl (Unit ⊕ Fin e))))))

lemma fieldPosition_spatialInside {K S : Type} {a b d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K)
    (h : K ⊕ S ≃ Fin a ⊕ Fin b) (e : ℕ) (y : Point d)
    (c : (Fin a ⊕ Fin b) ⊕ (Unit ⊕ Fin e) → Fin d) :
    CycleTrace.fieldPosition (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun a z => spatialInside F l (a ∘ h) z) e y c=
    spatialTensor F ((List.finRange e).map Sum.inl++l.map Sum.inr) y
      (c ∘ spatialFieldSlots h e) := by
  unfold CycleTrace.fieldPosition spatialInside spatialTensor
  rw [JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet_map]
  have he : (fun s => (c ∘ spatialFieldSlots h e) (Sum.inr s))=
      Sum.elim (fun s => c (Sum.inl (h (Sum.inr s)))) (fun _ => c (Sum.inr (Sum.inl ()))) := by
    funext s
    rcases s with s | u
    · rfl
    · cases u; rfl
  rw [he]
  rfl

lemma fieldPosition_spatialInside_allSplit {K S : Type} [Fintype K] [Fintype S] {a b d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l)
    (h : K ⊕ S ≃ Fin a ⊕ Fin b) (e : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound (CycleTrace.fieldPosition (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun a z => spatialInside F l (a ∘ h) z) e y)
      (spatialEnvelope F (Fintype.card K+e) y) := by
  have hh := spatialTensor_allSplit_envelope F (fun c => (hF c).smooth)
    ((List.finRange e).map Sum.inl++l.map Sum.inr)
    (JetCalculus.nodup_sum_append (List.nodup_finRange e) hl)
    (by intro k; cases k <;> simp [hall]) y
  have hhh := hh.reindex (spatialFieldSlots h e)
  simpa only [←fieldPosition_spatialInside,Fintype.card_sum,Fintype.card_fin,Nat.add_comm e] using hhh

lemma spatialInside_polySmooth {K S : Type} {d : ℕ}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (l : List K) (c : K ⊕ S → Fin d) (z : Fin d) : PolySmooth (spatialInside F l c z) :=
  (hF _).jet _ l

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal

def scoreField {d : ℕ} (H : Point d → ℝ) (c : Empty ⊕ Unit → Fin d) : Point d → ℝ :=
  directional (EuclideanSpace.basisFun (Fin d) ℝ (c (Sum.inr ()))) H

lemma scoreField_polySmooth {d : ℕ} {H : Point d → ℝ} (hH : PolySmooth H)
    (c : Empty ⊕ Unit → Fin d) : PolySmooth (scoreField H c) := hH.directional _

def lastSlot (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n+1) where
  toFun := Sum.elim Fin.castSucc (fun _ => Fin.last n)
  invFun := Fin.lastCases (Sum.inr ()) Sum.inl
  left_inv := by intro t; cases t <;> simp
  right_inv := by intro t; induction t using Fin.lastCases <;> simp

def scoreSpatialSlots (h : ℕ) : ((Fin h ⊕ Unit) ⊕ Unit) ≃ Fin (h+1) ⊕ (Empty ⊕ Unit) :=
  (lastSlot h).sumCongr (Equiv.emptySum Empty Unit).symm

lemma scoreSpatial_eq {d h : ℕ} (H : Point d → ℝ) (y : Point d)
    (c : Fin (h+1) ⊕ (Empty ⊕ Unit) → Fin d) :
    scoreAugmented H (List.finRange h) y (c ∘ scoreSpatialSlots h)=
      spatialTensor (scoreField H) (List.finRange (h+1)) y c := by
  unfold scoreAugmented spatialTensor scoreField
  rw [List.finRange_succ_last,JetCalculus.jet_append,JetCalculus.jet_map]
  rfl

lemma scoreField_spatial_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    (n : ℕ) (hn : 0<n) (y : Point d) :
    TensorEnergy.AllSplitBound (spatialTensor (scoreField (interpolationPotential F x r ρ)) (List.finRange n) y)
      (1+normalizedTensorMajorant (n+1) (1-ρ^2)) := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hh := (scoreAugmented_allSplit hF x hr hlam hl hρ0 hρ1 (List.finRange h)
    (List.nodup_finRange h) (by simp) y).reindex (scoreSpatialSlots h)
  simp only [scoreSpatial_eq,Fintype.card_fin] at hh
  apply hh.mono
  · exact add_nonneg (by split_ifs <;> norm_num) (normalizedTensorMajorant_nonneg _ _)
  · apply add_le_add _ le_rfl
    split_ifs <;> norm_num

lemma scoreField_spatial_arbitrary {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1)
    {K : Type} [Fintype K] [Nonempty K] (l : List K) (hlN : l.Nodup) (hall : ∀k,k∈l) (y : Point d) :
    TensorEnergy.AllSplitBound (spatialTensor (scoreField (interpolationPotential F x r ρ)) l y)
      (1+normalizedTensorMajorant (Fintype.card K+1) (1-ρ^2)) := by
  let e := (Fintype.equivFin K).symm
  have hp : ((List.finRange (Fintype.card K)).map e).Perm l :=
    fullList_perm ((List.nodup_finRange _).map e.injective) hlN
      (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩) hall
  have hs : ∀c,ContDiff ℝ (⊤:ℕ∞) (scoreField (interpolationPotential F x r ρ) c) := by
    intro c
    exact directional_smooth (interpolationPotential_smooth hF x hr.le hl hρ0 hρ1) _
  have hh := spatialTensor_allSplit_relabel (scoreField (interpolationPotential F x r ρ)) hs
    (Equiv.refl _) e (List.finRange (Fintype.card K)) l hp y _
    (scoreField_spatial_allSplit hF x hr hlam hl hρ0 hρ1 (Fintype.card K) Fintype.card_pos y)
  simpa only [Function.comp_def,Equiv.refl_apply] using hh

lemma spatialContractTerm_allSplit_nonempty {d : ℕ} {S T K : Type}
    [Fintype S] [Fintype T] [Fintype K]
    (p : K → Prop) [DecidablePred p]
    [Nonempty ({k // p k} ⊕ S)] [Nonempty ({k // ¬p k} ⊕ T)]
    {F : (S ⊕ Unit → Fin d) → Point d → ℝ}
    {G : (T ⊕ Unit → Fin d) → Point d → ℝ} {l : List K} {y : Point d} {M N : ℝ}
    (hF : TensorEnergy.AllSplitBound (spatialTensor F (selectList p l) y) M)
    (hG : TensorEnergy.AllSplitBound (spatialTensor G (selectList (fun k => ¬p k) l) y) N) :
    TensorEnergy.AllSplitBound (spatialContractTerm p F G l y) (M*N) :=
  ((extendedSpatial_allSplit hF).singleContract (extendedSpatial_allSplit hG)).reindex
    (contractSpatialSlots p)

end LogConcaveSampling

end

end

end

end OAI
