import Mathlib
import OAI.Probability.LogConcave.Sampling.ScoreSlots
import OAI.Probability.LogConcave.JetEstimates.ForestTensor

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

namespace TensorEnergy

lemma sum_fintype_irrel {α : Type} (i j : Fintype α) (f : α → ℝ) :
    @Finset.sum α ℝ _ (@Finset.univ α i) f = @Finset.sum α ℝ _ (@Finset.univ α j) f := by
  cases Subsingleton.elim i j
  rfl

def squared {S : Type} [Fintype S] {d : ℕ} (T : (S → Fin d) → ℝ) : ℝ := ∑c,(T c)^2
lemma squared_nonneg {S : Type} [Fintype S] {d : ℕ} (T : (S → Fin d) → ℝ) : 0 ≤ squared T :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
lemma squared_reindex {S T : Type} [Fintype S] [Fintype T] {d : ℕ}
    (A : (S → Fin d) → ℝ) (e : S ≃ T) : squared (fun c => A (c ∘ e))=squared A := by
  exact Equiv.sum_comp ((Equiv.arrowCongr e (Equiv.refl (Fin d))).symm) (fun c => (A c)^2)
lemma squared_sum {S I : Type} [Fintype S] {d : ℕ} (s : Finset I)
    (A : I → (S → Fin d) → ℝ) :
    squared (fun c => ∑i∈s,A i c) ≤ s.card*(∑i∈s,squared (A i)) := by
  apply (Finset.sum_le_sum (fun _ _ => sq_sum_le_card_mul_sum_sq)).trans_eq
  rw [←Finset.mul_sum,Finset.sum_comm]
  rfl
lemma squared_add {S : Type} [Fintype S] {d : ℕ} (A B : (S → Fin d) → ℝ) :
    squared (fun c => A c+B c) ≤ 2*(squared A+squared B) := by
  apply (Finset.sum_le_sum (fun c _ => show (A c+B c)^2 ≤ 2*((A c)^2+(B c)^2) by nlinarith [sq_nonneg (A c-B c)])).trans_eq
  simp only [squared]
  rw [←Finset.mul_sum,←Finset.sum_add_distrib]
lemma squared_zero {S : Type} [Fintype S] {d : ℕ} : squared (fun _ : S → Fin d => (0:ℝ))=0 := by
  simp [squared]
end TensorEnergy
open TensorEnergy

def spatialSquared {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (y : Point d) : ℝ :=
  squared (spatialTensor F (List.finRange j) y)
lemma spatialSquared_nonneg {S : Type} [Fintype S] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (y : Point d) : 0  ≤  spatialSquared F j y := squared_nonneg _

lemma spatialSquared_full {S K : Type} [Fintype S] [Fintype K] {d : ℕ}
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d) :
    squared (spatialTensor F l y)=spatialSquared F (Fintype.card K) y := by
  let e := (Fintype.equivFin K).symm
  have hp : ((List.finRange (Fintype.card K)).map e).Perm l :=
    fullList_perm ((List.nodup_finRange _).map e.injective) hl
      (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩) hall
  have hh := squared_reindex (spatialTensor F (List.finRange (Fintype.card K)) y) (e.sumCongr (Equiv.refl S))
  have he : (fun c => spatialTensor F (List.finRange (Fintype.card K)) y (c ∘ (e.sumCongr (Equiv.refl S))))=
      spatialTensor F l y := by
    funext c
    simpa only [Function.comp_def,Equiv.refl_apply] using
      spatialTensor_relabel F hF (Equiv.refl S) e _ _ hp y c
  rw [he] at hh
  exact hh

lemma extendedSpatial_squared {d : ℕ} {S K : Type} [Fintype S] [Fintype K]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d) :
    squared (extendedSpatial F l y)=squared (spatialTensor F l y) :=
  squared_reindex _ (Equiv.sumAssoc K S Unit).symm

lemma spatialContractTerm_squared {d : ℕ} {S T K : Type} [Fintype S]
    [Fintype T] [Fintype K] (p : K → Prop) [DecidablePred p] [Nonempty ({k // p k} ⊕ S)]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c))
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d) {M : ℝ}
    (hF : AllSplitBound (spatialTensor F (selectList p l) y) M) :
    squared (spatialContractTerm p F G l y) ≤ M^2*spatialSquared G (Fintype.card {k // ¬p k}) y := by
  have hr := squared_reindex
    (singleContract (extendedSpatial F (selectList p l) y)
      (extendedSpatial G (selectList (fun k => ¬p k) l) y)) (contractSpatialSlots p)
  change squared (spatialContractTerm p F G l y)=_ at hr
  rw [hr]
  have ha : AllSplitBound (extendedSpatial F (selectList p l) y) M := extendedSpatial_allSplit hF
  have hh := AllSplitBound.singleContract_frobenius ha (extendedSpatial G (selectList (fun k => ¬p k) l) y)
  have he : squared (extendedSpatial G (selectList (fun k => ¬p k) l) y)=
      spatialSquared G (Fintype.card {k // ¬p k}) y := by
    rw [extendedSpatial_squared,spatialSquared_full G hG _
      (selectList_nodup _ hl) (selectList_full _ hall)]
  exact (sum_fintype_irrel _ _ _).trans_le (hh.trans_eq
    (congrArg (fun x => M^2*x) ((sum_fintype_irrel _ _ _).trans he)))

lemma spatialSquared_contract {d j : ℕ} {S T : Type} [Fintype S] [Nonempty S] [Fintype T]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,ContDiff ℝ (⊤:ℕ∞) (F c)) (hG : ∀c,ContDiff ℝ (⊤:ℕ∞) (G c))
    (M : ℕ → ℝ) (y : Point d)
    (hb : ∀k ≤ j,AllSplitBound (spatialTensor F (List.finRange k) y) (M k)) :
    spatialSquared (fun a z => singleContract (fun c => F c z) (fun c => G c z) a) j y ≤
      2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset,(M s.card)^2*spatialSquared G (j-s.card) y := by
  let : DecidableEq (Fin j) := Classical.decEq _
  have heq : (List.finRange j).toFinset=(Finset.univ : Finset (Fin j)) := by ext k; simp
  have he : spatialTensor (fun a z => singleContract (fun c => F c z) (fun c => G c z) a) (List.finRange j) y=
      fun c => ∑s∈(Finset.univ : Finset (Fin j)).powerset,
        spatialContractTerm (fun k => k∈s) F G (List.finRange j) y c := by
    funext c
    simpa only [heq] using spatialTensor_singleContract F G hF hG _ (List.nodup_finRange _) y c
  unfold spatialSquared
  rw [he]
  apply (TensorEnergy.squared_sum _ _).trans
  simp only [Finset.card_powerset,Finset.card_univ,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro s _
  have hs : s.card ≤ j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
  have hr : AllSplitBound (spatialTensor F (selectList (fun k => k∈s) (List.finRange j)) y) (M s.card) := by
    let e := (Fintype.equivFin s).symm
    have hp : ((List.finRange (Fintype.card s)).map e).Perm
        (selectList (fun k => k∈s) (List.finRange j)) :=
      fullList_perm ((List.nodup_finRange _).map e.injective) (selectList_nodup _ (List.nodup_finRange _))
        (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩)
        (selectList_full _ (by simp))
    have hcard : Fintype.card s=s.card := Fintype.card_of_subtype s (fun _ => Iff.rfl)
    have hh := spatialTensor_allSplit_relabel F hF (Equiv.refl _) e _ _ hp y (M s.card)
      (by rw [hcard]; exact hb s.card hs)
    simpa only [Function.comp_def,Equiv.refl_apply] using hh
  have hcard : Fintype.card {k : Fin j // k∉s}=j-s.card := by
    rw [Fintype.card_subtype_compl]
    have hc : Fintype.card {k : Fin j // k∈s}=s.card := Fintype.card_of_subtype s (fun _ => Iff.rfl)
    rw [hc,Fintype.card_fin]
  have hh := spatialContractTerm_squared (fun k => k∈s) F G hG _ (List.nodup_finRange _) (by simp) y hr
  simp only [Fintype.card_eq_nat_card] at hcard hh
  rw [hcard] at hh
  exact hh

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators NNReal
open TensorEnergy

lemma PolySmooth.sq {d : ℕ} {f : Point d → ℝ} (hf : PolySmooth f) : PolySmooth (fun y => (f y)^2) := by
  simpa only [pow_two] using hf.mul hf

lemma spatialSquared_polySmooth {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) (j : ℕ) :
    PolySmooth (spatialSquared F j) :=
  PolySmooth.sum _ (fun c _ => (spatialTensor_polySmooth F hF _ c).sq)

def spatialEnergy {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (μ : Measure (Point d)) : ℝ :=
  ∫y,spatialSquared F j y ∂μ
lemma spatialEnergy_nonneg {d : ℕ} {S : Type} [Fintype S]
    (F : (S → Fin d) → Point d → ℝ) (j : ℕ) (μ : Measure (Point d)) :
    0  ≤  spatialEnergy F j μ := integral_nonneg (spatialSquared_nonneg F j)

lemma singleContract_polySmooth {d : ℕ} {S T : Type}
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c))
    (a : S ⊕ T → Fin d) :
    PolySmooth (fun y => singleContract (fun c => F c y) (fun c => G c y) a) :=
  PolySmooth.sum _ (fun _z _ => (hF _).mul (hG _))

lemma spatialEnergy_contract {d j : ℕ} {S T : Type} [Fintype S] [Nonempty S] [Fintype T]
    {H : Point d → ℝ} (hH : Continuous H) (ht : HasGaussianLowerTail H)
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ)
    (G : (T ⊕ Unit → Fin d) → Point d → ℝ)
    (hF : ∀c,PolySmooth (F c)) (hG : ∀c,PolySmooth (G c)) (M : ℕ → ℝ)
    (hb : ∀k ≤ j,∀y,AllSplitBound (spatialTensor F (List.finRange k) y) (M k)) :
    spatialEnergy (fun a y => singleContract (fun c => F c y) (fun c => G c y) a) j (gibbs H) ≤
      2^j*∑s∈(Finset.univ : Finset (Fin j)).powerset,(M s.card)^2*spatialEnergy G (j-s.card) (gibbs H) := by
  have hs (k : ℕ) := (spatialSquared_polySmooth G hG k).integrable hH ht
  have hi := (spatialSquared_polySmooth _ (singleContract_polySmooth F G hF hG) j).integrable hH ht
  have hj := (integrable_finsetSum (Finset.univ : Finset (Fin j)).powerset
    (fun s _ => (hs (j-s.card)).const_mul ((M s.card)^2))).const_mul ((2:ℝ)^j)
  apply (integral_mono hi hj (fun y => spatialSquared_contract F G (fun c => (hF c).smooth)
    (fun c => (hG c).smooth) M y (fun k hk => hb k hk y))).trans_eq
  rw [integral_const_mul,integral_finsetSum _ (fun s _ => (hs (j-s.card)).const_mul ((M s.card)^2))]
  simp only [integral_const_mul,spatialEnergy]

def insideZeroColor (K S : Type) (d : ℕ) :
    ((K ⊕ S → Fin d) × Fin d) ≃ (K ⊕ (S ⊕ Unit) → Fin d) where
  toFun p := Sum.elim (fun k => p.1 (Sum.inl k)) (Sum.elim (fun s => p.1 (Sum.inr s)) (fun _ => p.2))
  invFun c := (Sum.elim (fun k => c (Sum.inl k)) (fun s => c (Sum.inr (Sum.inl s))),c (Sum.inr (Sum.inr ())))
  left_inv p := by apply Prod.ext; funext a; cases a <;> rfl; rfl
  right_inv c := by funext a; rcases a with a | (a | a); rfl; rfl; cases a; rfl

def insideOneColor (K S : Type) (d : ℕ) :
    ((K ⊕ S → Fin d) × Fin d × Fin d) ≃ ((Unit ⊕ K) ⊕ (S ⊕ Unit) → Fin d) where
  toFun p := Sum.elim (Sum.elim (fun _ => p.2.1) (fun k => p.1 (Sum.inl k)))
    (Sum.elim (fun s => p.1 (Sum.inr s)) (fun _ => p.2.2))
  invFun c := (Sum.elim (fun k => c (Sum.inl (Sum.inr k))) (fun s => c (Sum.inr (Sum.inl s))),
    c (Sum.inl (Sum.inl ())),c (Sum.inr (Sum.inr ())))
  left_inv p := by apply Prod.ext; funext a; cases a <;> rfl; rfl
  right_inv c := by funext a; rcases a with (a | a) | (a | a); cases a; rfl; rfl; rfl; cases a; rfl

lemma spatialInside_zero_squared {d : ℕ} {S K : Type} [Fintype S] [Fintype K]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d) :
    (∑c,∑z : Fin d,(spatialInside F l c z y)^2)=squared (spatialTensor F l y) := by
  have hh := Equiv.sum_comp (insideZeroColor K S d) (fun c => (spatialTensor F l y c)^2)
  rw [Fintype.sum_prod_type] at hh
  exact hh.trans (sum_fintype_irrel _ _ _)

lemma spatialInside_one_squared {d : ℕ} {S K : Type} [Fintype S] [Fintype K]
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (l : List K) (y : Point d) :
    (∑c,∑i : Fin d,∑z : Fin d,(directional (EuclideanSpace.basisFun (Fin d) ℝ i)
      (spatialInside F l c z) y)^2)=
      squared (spatialTensor F (([()] : List Unit).map Sum.inl++l.map Sum.inr) y) := by
  have hh := Equiv.sum_comp (insideOneColor K S d)
    (fun c => (spatialTensor F (([()] : List Unit).map Sum.inl++l.map Sum.inr) y c)^2)
  simp only [Fintype.sum_prod_type] at hh
  refine Eq.trans ?_ (hh.trans (sum_fintype_irrel _ _ _))
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro z _
  unfold spatialTensor spatialInside
  rw [JetCalculus.jet_append,JetCalculus.jet_map,JetCalculus.jet_map]
  rfl

lemma spatialAdjointLeading_energy {d j : ℕ} {S : Type} [Fintype S]
    {H : Point d → ℝ} (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (F : (S ⊕ Unit → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c)) :
    (∫y,squared (spatialAdjointLeading H F (List.finRange j) y) ∂gibbs H) ≤
      spatialEnergy F (j+1) (gibbs H)+(K:ℝ)*spatialEnergy F j (gibbs H) := by
  let V := spatialInside F (List.finRange j)
  have hV c z : PolySmooth (V c z) := spatialInside_polySmooth F hF _ c z
  have hi c := (hH.tensorAdjoint (hV c) (EuclideanSpace.basisFun (Fin d) ℝ)).sq.integrable hH.smooth.continuous ht
  have hi0 c := integrable_square_sum hH.smooth.continuous ht (fun z => (hV c z).polyC1)
  have hi1 c := integrable_directional_square_sum hH.smooth.continuous ht (EuclideanSpace.basisFun (Fin d) ℝ)
    (fun _ z => ((hV c z).directional _).polyC1)
  have hh := tensorAdjoint_frobenius_squared hH.smooth ht hL (EuclideanSpace.basisFun (Fin d) ℝ)
    (fun c z => (hV c z).smooth) (fun c z => (hV c z).polyC1) (fun c _ z => ((hV c z).directional _).polyC1)
  rw [←integral_finsetSum _ (fun c _ => hi c),←integral_finsetSum _ (fun c _ => hi1 c),
    ←integral_finsetSum _ (fun c _ => hi0 c)] at hh
  have hleft : (∫y,squared (spatialAdjointLeading H F (List.finRange j) y) ∂gibbs H)=
      ∫y,∑c,(tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ) (V c) y)^2 ∂gibbs H := by
    apply integral_congr_ae
    filter_upwards [] with y
    exact sum_fintype_irrel _ _ _
  rw [←hleft] at hh
  have hz (y : Point d) : (∑c,∑z : Fin d,(V c z y)^2)=spatialSquared F j y := by
    exact (sum_fintype_irrel _ _ _).trans (spatialInside_zero_squared F _ y)
  have he (y : Point d) := spatialSquared_full F (fun c => (hF c).smooth)
    (([()] : List Unit).map Sum.inl++(List.finRange j).map Sum.inr)
    (JetCalculus.nodup_sum_append (by simp) (List.nodup_finRange _))
    (by intro a; cases a <;> simp) y
  simp only [Fintype.card_sum,Fintype.card_unique,Fintype.card_fin,Nat.add_comm 1] at he
  have ho (y : Point d) : (∑c,∑i : Fin d,∑z : Fin d,
      (directional (EuclideanSpace.basisFun (Fin d) ℝ i) (V c z) y)^2)=spatialSquared F (j+1) y := by
    exact (sum_fintype_irrel _ _ _).trans ((spatialInside_one_squared F _ y).trans (he y))
  simp_rw [hz,ho] at hh
  exact hh

end LogConcaveSampling

end

end

end

end OAI
