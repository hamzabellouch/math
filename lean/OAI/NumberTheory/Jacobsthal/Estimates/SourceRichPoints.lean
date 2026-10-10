import OAI.NumberTheory.Jacobsthal.Partitions.SourceRefinedCell

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosInverseTail

theorem commonParentLength_le_ratio (Y p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (Qplus : ℝ) (hqQ : (q : ℝ) ≤ Qplus) :
    (commonParentLength Y p Qplus : ℝ) ≤ (Y : ℝ)/((p : ℝ)*q) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Qplus := hqR.trans_le hqQ
  exact (Nat.floor_le (by positivity : 0 ≤ (Y : ℝ)/((p : ℝ)*Qplus))).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hpR hqR)
      (mul_le_mul_of_nonneg_left hqQ hpR.le))

theorem strict_deviation_transfer (A B m e u T delta : ℝ) (hu : 0 < u)
    (hT : 0 ≤ T) (hd : 0 < delta) (hbad : delta*T < |B-A/u|)
    (herr : |B-e|+|A-m|/u ≤ (delta/2)*T) :
    (delta/4)*T < |e-m/u| := by
  have htri : |B-A/u| ≤ |B-e|+|e-m/u|+|A-m|/u := by
    calc
      _ ≤ |B-e|+|e-A/u| := abs_sub_le B e (A/u)
      _ ≤ |B-e|+(|e-m/u|+|m/u-A/u|) := add_le_add le_rfl (abs_sub_le e (m/u) (A/u))
      _ = _ := by rw [← sub_div,abs_div,abs_of_pos hu,abs_sub_comm m A];ring
  nlinarith

end ErdosInverseTail

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseTail
open NumberTheoryLean ErdosInverseHits ErdosInverseFrozen ErdosInverseEuler ErdosInverseCounts ErdosInverseBoxHeight

theorem source_bad_edge_implies_frozen (aStar delta : ℝ) (ha : 0 < aStar) (hd : 0 < delta) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,∀ (a : ℕ → ℕ) (p q q0 u : ℕ) [NeZero p] [NeZero u]
        (_hp : p.Prime) (_hu : u.Prime) (hqp : q.Coprime p) (hq : Squarefree q)
        (hpu : p.Coprime u) (hqu : q.Coprime u) (Qplus : ℝ) (b0 v : ℤ),
        (q : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q : ℝ) →
        3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z) →
        (∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q*u).Coprime t) →
        Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (q0 : ℤ) →
        Int.ModEq (smallModulus (sourceW z) : ℤ) (primeHitRepresentative q hq a : ℤ) b0 →
        Int.ModEq (smallModulus (sourceW z) : ℤ)
          (parentSlope p q hqp (a p) (primeHitRepresentative q hq a) : ℤ) v →
        WitnessingBadEdge (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
          (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) p q u →
        parentEdgeResidue p q u hqp hq hpu hqu a ∈
          frozenExceptional (commonParentLength (sourceY z) p Qplus) (sourceW z) p q0 b0 v a u
            (delta/4) (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) := by
  obtain ⟨C,hC,hreplacement⟩ := source_interval_replacement aStar ha
  have hden : 0 < 12*C := by positivity
  refine ⟨min 1 (delta/(12*C)),lt_min zero_lt_one (div_pos hd hden),min_le_left _ _,?_⟩
  intro xi hxi hxibound
  have hxi1 : xi ≤ 1 := hxibound.trans (min_le_left _ _)
  have hxiBudget := (le_div_iff₀ hden).mp (hxibound.trans (min_le_right _ _))
  have hbudget : 6*C*xi ≤ delta/2 := by nlinarith
  filter_upwards [hreplacement xi hxi hxi1,sourceW_tendsto_atTop.eventually_ge_atTop 2] with z hrepl hw
  intro a p q q0 u instP instU hp hu hqp hq hpu hqu Qplus b0 v hqQ hQq hlog hcop hqq hbb hsv hbad
  let J := commonParentLength (sourceY z) p Qplus
  let V0 := SmallSieveFinite.smallEuler ⌊sourceW z⌋₊
  let A : ℝ := modulusCount (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a (p*q)
  let B : ℝ := modulusCount (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a (p*q*u)
  let m : ℝ := (frozenCoordinates J (sourceW z) p q0 b0 v a).card
  let e : ℝ := ((frozenCoordinates J (sourceW z) p q0 b0 v a).filter
    (fun j : ℕ => (j : ZMod u) = parentEdgeResidue p q u hqp hq hpu hqu a)).card
  let T : ℝ := (J : ℝ)*V0/(u : ℝ)
  have huR : (0 : ℝ) < u := by exact_mod_cast hu.pos
  have hwpos : 0 < sourceW z := by linarith
  have hV : 0 < V0 := (inv_pos.mpr hwpos).trans_le (SmallSieveFinite.smallEuler_floor_ge_inv (sourceW z) hw)
  have hT : 0 ≤ T := by dsimp [T];positivity
  have herr := hrepl a p q q0 u hp hu hqp hq hpu hqu Qplus b0 v hqQ hQq hlog hcop hqq hbb hsv
  change |A-m| ≤ 2*C*xi*(J : ℝ)*V0 ∧ |B-e| ≤ 4*C*xi*(J : ℝ)*V0/(u : ℝ) at herr
  have hJR := commonParentLength_le_ratio (sourceY z) p q hp.pos (Nat.pos_of_ne_zero hq.ne_zero) Qplus hqQ
  have hnorm : delta*T ≤ delta*(sourceY z : ℝ)*V0/((p : ℝ)*q*u) := by
    calc
      _ = (delta*V0/(u : ℝ))*(J : ℝ) := by dsimp [T];ring
      _ ≤ (delta*V0/(u : ℝ))*((sourceY z : ℝ)/((p : ℝ)*q)) :=
        mul_le_mul_of_nonneg_left hJR (by positivity)
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev];ring
  have hbad' : delta*(sourceY z : ℝ)*V0/((p : ℝ)*q*u) < |B-A/(u : ℝ)| := by
    simpa only [WitnessingBadEdge,NodeBadEdge,Nat.cast_mul] using hbad
  have herrsum : |B-e|+|A-m|/(u : ℝ) ≤ (delta/2)*T := by
    calc
      _ ≤ 4*C*xi*(J : ℝ)*V0/(u : ℝ)+(2*C*xi*(J : ℝ)*V0)/(u : ℝ) :=
        add_le_add herr.2 (div_le_div_of_nonneg_right herr.1 huR.le)
      _ = (6*C*xi)*T := by dsimp [T];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hT
  have hdev := strict_deviation_transfer A B m e (u : ℝ) T delta huR hT hd
    (hnorm.trans_lt hbad') herrsum
  rw [mem_frozenExceptional]
  change (delta/4)*(J : ℝ)*V0/(u : ℝ) < |e-m/(u : ℝ)|
  simpa only [T,mul_div_assoc,mul_assoc] using hdev

end ErdosInverseTail

end

section

namespace ErdosInverseRefinement
open ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost ErdosInverseHits ErdosInverseStructured
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem selectedRow_subset_nonstructured (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp : ℝ) (P U : Finset ℕ) (h : ℕ) (hh : 0 < h) (s : Sample U h)
    (T : ℕ → Finset ℤ) (q : ℕ) (hP : ∀ p ∈ P,p.Prime) (hqp : ∀ p ∈ P,q.Coprime p)
    (htest : ∀ p ∈ P,∀ [NeZero p],∀ hcop : q.Coprime p,
      p ∈ selectedRow P U (actualWitness Y small a delta V0 P S R Z cp) h s q →
      (parentSlope p q hcop (a p) (cofactorHit q a) : ℤ) ∈ T p) :
    selectedRow P U (actualWitness Y small a delta V0 P S R Z cp) h s q ⊆
      nonstructuredPrimes P (fun p => (a p : ℤ)) T S R Z cp (cofactorPoint a q) := by
  intro p hp
  have hm := Finset.mem_filter.mp hp
  let : NeZero p := ⟨(hP p hm.1).ne_zero⟩
  have hn := (hm.2 ⟨0,hh⟩).1
  apply Finset.mem_filter.mpr
  refine ⟨hm.1,?_⟩
  refine ⟨parentSlope_incidence a T p q (hqp p hm.1) (htest p hm.1 (hqp p hm.1) hp),?_⟩
  simpa only [cofactorPoint,Int.toNat_natCast] using hn

theorem rich_points_incidence (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (delta V0 S R Z cp gamma : ℝ) (D P U : Finset ℕ) (h : ℕ) (hh : 0 < h) (s : Sample U h)
    (T : ℕ → Finset ℤ) (hP : ∀ p ∈ P,p.Prime) (hPpos : 0 < P.card)
    (hqp : ∀ q ∈ D,∀ p ∈ P,q.Coprime p)
    (htest : ∀ q ∈ D,∀ p ∈ P,∀ [NeZero p],∀ hcop : q.Coprime p,
      p ∈ selectedRow P U (actualWitness Y small a delta V0 P S R Z cp) h s q →
      (parentSlope p q hcop (a p) (cofactorHit q a) : ℤ) ∈ T p) :
    ∀ v ∈ cofactorPoints (richCofactors D P U (actualWitness Y small a delta V0 P S R Z cp) h s gamma) a,
      (gamma/8)*(P.card : ℝ) ≤
        ((nonstructuredPrimes P (fun p => (a p : ℤ)) T S R Z cp v).card : ℝ) := by
  intro v hv
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
  have hqD := richCofactors_subset D P U _ h s gamma hq
  calc
    _ ≤ ((selectedRow P U (actualWitness Y small a delta V0 P S R Z cp) h s q).card : ℝ) :=
      richCofactor_row_card D P U _ h s gamma hPpos q hq
    _ ≤ _ := by
      exact_mod_cast Finset.card_le_card (selectedRow_subset_nonstructured Y small a delta V0 S R Z cp
        P U h hh s T q hP (hqp q hqD) (htest q hqD))

end ErdosInverseRefinement

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseRefinement
open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost
  ErdosInverseCRT ErdosInverseEuler ErdosInverseHits ErdosInverseStructured ErdosInverseTail
  ErdosInverseBoxHeight

theorem source_parentSlope_mem (aStar delta : ℝ) (ha : 0 < aStar) (hd : 0 < delta) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,∀ (P U C : Finset ℕ) (a : ℕ → ℕ) (h : ℕ) (s : Sample U h)
        (_hU : ∀ u ∈ U,u.Prime) (hpU : ∀ p ∈ P,∀ u ∈ U,p.Coprime u)
        (qRef : ℕ) (hqRef : ∀ u ∈ U,qRef.Coprime u)
        (j : RefinementLabel (sampleModulus U h s))
        (q p qInitial : ℕ) [NeZero p] (bInitial : ℤ) (Qplus : ℝ)
        (_hp : p.Prime) (_hpP : p ∈ P) (hqp : q.Coprime p) (_hq : Squarefree q)
        (_hqU : ∀ u ∈ U,q.Coprime u),
        q ∈ refinementCell C a (sampleModulus U h s) j →
        qRef ∈ refinementCell C a (sampleModulus U h s) j →
        (q : ℝ) ≤ Qplus → Qplus ≤ (1+xi)*(q : ℝ) →
        (∀ u ∈ U,3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
        (∀ u ∈ U,∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q*u).Coprime t) →
        Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (qInitial : ℤ) →
        Int.ModEq (smallModulus (sourceW z) : ℤ) (cofactorHit q a : ℤ) bInitial →
        (∀ i : Fin h,ErdosInverseCounts.WitnessingBadEdge (sourceY z)
          (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
          (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) p q (s i).val) →
        (parentSlope p q hqp (a p) (cofactorHit q a) : ℤ) ∈
          pointSlopes (sourceY z) (sourceW z) Qplus qInitial bInitial a (delta/4)
            P U h s hpU qRef (cofactorHit qRef a) hqRef p := by
  obtain ⟨xi0,hxi0,hxi01,htransfer⟩ := source_bad_edge_implies_frozen aStar delta ha hd
  refine ⟨xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  filter_upwards [htransfer xi hxi hxib] with z hz
  intro P U C a h s hU hpU qRef hqRef j q p qInitial instP bInitial Qplus hp hpP hqp hq hqU
    hqC hRefC hqQ hQq hlog hsmall hqq hbb hbad
  let : NeZero (smallModulus (sourceW z)) := ⟨(smallModulus_pos _).ne'⟩
  let t : ℤ := parentSlope p q hqp (a p) (cofactorHit q a)
  have ht : t ∈ Finset.Ico (0 : ℤ) (p : ℤ) := by
    apply Finset.mem_Ico.mpr
    refine ⟨Int.natCast_nonneg _,?_⟩
    dsimp only [t]
    exact_mod_cast parentSlope_lt p q hqp (a p) (cofactorHit q a)
  have hts : Int.ModEq (smallModulus (sourceW z) : ℤ) t
      ((t : ZMod (smallModulus (sourceW z))).val : ℤ) := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val]
  rw [pointSlopes_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpP]
  apply mem_sourceTestedSlopes_of_same_cell p q qRef _ (fun i => (s i).val)
    (fun i => hpU p hpP _ (s i).property) (fun i => hqU _ (s i).property)
    (fun i => hqRef _ (s i).property) (fun u => (a u : ℤ))
    (cofactorHit q a) (cofactorHit qRef a) t _ ht
  · intro i
    exact (refinement_sample_congruences C U a h s j q qRef hqC hRefC i).1
  · intro i
    simpa only [Int.cast_natCast] using
      (refinement_sample_congruences C U a h s j q qRef hqC hRefC i).2
  · intro i
    let : NeZero (s i).val := ⟨(hU _ (s i).property).ne_zero⟩
    have hbb' : Int.ModEq (smallModulus (sourceW z) : ℤ)
        (primeHitRepresentative q hq a : ℤ) bInitial := by
      simpa only [cofactorHit_eq q hq a] using hbb
    have hts' : Int.ModEq (smallModulus (sourceW z) : ℤ)
        (parentSlope p q hqp (a p) (primeHitRepresentative q hq a) : ℤ)
        ((t : ZMod (smallModulus (sourceW z))).val : ℤ) := by
      simpa only [t,cofactorHit_eq q hq a] using hts
    have he := hz a p q qInitial (s i).val hp (hU _ (s i).property) hqp hq
      (hpU p hpP _ (s i).property) (hqU _ (s i).property) Qplus bInitial
      ((t : ZMod (smallModulus (sourceW z))).val : ℤ) hqQ hQq
      (hlog _ (s i).property) (hsmall _ (s i).property) hqq hbb' hts' (hbad i)
    simpa only [actualFamily,parentEdgeResidue,t,cofactorHit_eq q hq a] using he

end ErdosInverseRefinement

end

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseRefinement
open NumberTheoryLean ErdosInverseCells ErdosInverseSampling ErdosInverseSampleCost
  ErdosInverseEuler ErdosInverseHits ErdosInverseStructured ErdosInverseTail
  ErdosInverseBoxHeight ErdosInversePrimeBin ErdosConvexGraph

theorem source_rich_points (aStar delta K gamma : ℝ) (h : ℕ)
    (ha : 0 < aStar) (hd : 0 < delta) (hK : 0 ≤ K) (hg : 0 < gamma) (hh : 0 < h) :
    ∃ xi0 : ℝ,0 < xi0 ∧ xi0 ≤ 1 ∧ ∀ xi : ℝ,0 < xi → xi ≤ xi0 →
      ∀ᶠ z : ℝ in atTop,∀ (P C : Finset ℕ) (a : ℕ → ℕ) (U theta Qplus S R cp : ℝ)
        (qInitial : ℕ) (bInitial : ℤ),
        0 < R → 0 < S → sourceW z ≤ U → U ≤ (sourceW z)^K → 0 ≤ theta → theta ≤ 1 →
        0 < P.card → (∀ p ∈ P,p.Prime) →
        (∀ p ∈ P,∀ u ∈ primeBin U theta,p.Coprime u) →
        (∀ q ∈ C,Squarefree q ∧ (q : ℝ) ≤ S) →
        (∀ q ∈ C,∀ p ∈ P,q.Coprime p) →
        (∀ q ∈ C,∀ u ∈ primeBin U theta,q.Coprime u) →
        (∀ q ∈ C,(q : ℝ) ≤ Qplus ∧ Qplus ≤ (1+xi)*(q : ℝ)) →
        (∀ q ∈ C,∀ p ∈ P,∀ u ∈ primeBin U theta,
          3*aStar/4 ≤ Real.log ((sourceY z : ℝ)/((p : ℝ)*q*u))/Real.log (sourceW z)) →
        (∀ q ∈ C,∀ p ∈ P,∀ u ∈ primeBin U theta,
          ∀ t : ℕ,t.Prime → (t : ℝ) ≤ sourceW z → (p*q*u).Coprime t) →
        (∀ q ∈ C,Int.ModEq (smallModulus (sourceW z) : ℤ) (q : ℤ) (qInitial : ℤ) ∧
          Int.ModEq (smallModulus (sourceW z) : ℤ) (cofactorHit q a : ℤ) bInitial) →
        S/sourceZ z ≤ (C.card : ℝ) →
        ∀ s : Sample (primeBin U theta) h,
          gamma/2 ≤ selectedFraction (P.product C) (primeBin U theta)
            (actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
              (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) cp) h s →
          actualCost (sourceY z) (sourceW z) Qplus R qInitial bInitial a (delta/4)
            P (primeBin U theta) h s ≤ 1/(Real.log z)^6 →
          ∃ (T : ℕ → Finset ℤ) (D : Finset ℕ),D ⊆ C ∧
            (∀ v ∈ cofactorPoints D a,InSquare S v) ∧
            Set.InjOn Prod.fst (cofactorPoints D a : Set (ℤ × ℤ)) ∧
            S/(sourceZ z)^4 ≤ ((cofactorPoints D a).card : ℝ) ∧
            (∀ v ∈ cofactorPoints D a,∀ ell ∈ v.1.toNat.primeFactors,
              (v.2 : ZMod ell) = (a ell : ZMod ell)) ∧
            (∀ v ∈ cofactorPoints D a,(gamma/8)*(P.card : ℝ) ≤
              ((nonstructuredPrimes P (fun p => (a p : ℤ)) T S R (sourceZ z) cp v).card : ℝ)) ∧
            (∑ p ∈ P,((T p).card : ℝ)) ≤ (P.card : ℝ)*R/(Real.log z)^6 := by
  classical
  obtain ⟨xi0,hxi0,hxi01,hparent⟩ := source_parentSlope_mem aStar delta ha hd
  refine ⟨xi0,hxi0,hxi01,?_⟩
  intro xi hxi hxib
  filter_upwards [hparent xi hxi hxib,source_refined_cell K gamma h hK hg,
    sourceZ_tendsto_atTop.eventually_ge_atTop (8/gamma),sourceW_tendsto_atTop.eventually_ge_atTop 2]
    with z hparentZ hrefine hZlarge hW
  intro P C a U theta Qplus S R cp qInitial bInitial hR hS hWU hUtop htheta htheta1 hPpos hP
    hpU hCsq hCP hCU hCQ hlog hsmall hcong hCsize s hreward hcost
  have hW0 : 0 ≤ sourceW z := by linarith
  have hU0 : 0 ≤ U := hW0.trans hWU
  let Uset := primeBin U theta
  have hUprime : ∀ u ∈ Uset,u.Prime := fun u hu => ((mem_primeBin hU0 htheta u).mp hu).1
  have huLarge : ∀ u ∈ Uset,sourceW z < (u : ℝ) := by
    intro u hu
    exact hWU.trans_lt ((mem_primeBin hU0 htheta u).mp hu).2.1
  let witness := actualWitness (sourceY z) (LargePrimeDeletion.cutoffPrimes ⌊sourceW z⌋₊) a delta
    (SmallSieveFinite.smallEuler ⌊sourceW z⌋₊) P S R (sourceZ z) cp
  obtain ⟨j,hjSize,hjNonempty,hjReward⟩ := hrefine U theta hU0 hUtop htheta htheta1 s P C a
    witness S hPpos hS hCsize hreward
  let C' := refinementCell C a (sampleModulus Uset h s) j
  have hC'C : C' ⊆ C := fun q hq => (mem_refinementCell C a _ j q).mp hq |>.1
  obtain ⟨qRef,hqRef⟩ := hjNonempty
  have hRefU : ∀ u ∈ Uset,qRef.Coprime u := hCU qRef (hC'C hqRef)
  let T := pointSlopes (sourceY z) (sourceW z) Qplus qInitial bInitial a (delta/4)
    P Uset h s hpU qRef (cofactorHit qRef a) hRefU
  let D := richCofactors C' P Uset witness h s gamma
  have hDC' : D ⊆ C' := richCofactors_subset C' P Uset witness h s gamma
  have hDC : D ⊆ C := hDC'.trans hC'C
  have hZ : 0 < sourceZ z := Real.exp_pos _
  have hInv : 1/sourceZ z ≤ gamma/8 := by
    apply (div_le_iff₀ hZ).mpr
    have hmul := (div_le_iff₀ hg).mp hZlarge
    nlinarith
  have htests : ∀ q ∈ C',∀ p ∈ P,∀ [NeZero p],∀ hcop : q.Coprime p,
      p ∈ selectedRow P Uset witness h s q →
      (parentSlope p q hcop (a p) (cofactorHit q a) : ℤ) ∈ T p := by
    intro q hq p hp instP hcop hselected
    have hqC := hC'C hq
    have hselected' := Finset.mem_filter.mp hselected
    exact hparentZ P Uset C a h s hUprime hpU qRef hRefU j q p qInitial bInitial Qplus
      (hP p hp) hp hcop (hCsq q hqC).1 (hCU q hqC) hq hqRef
      (hCQ q hqC).1 (hCQ q hqC).2 (hlog q hqC p hp) (hsmall q hqC p hp)
      (hcong q hqC).1 (hcong q hqC).2 (fun i => (hselected'.2 i).2)
  refine ⟨T,D,hDC,cofactorPoints_square D a S (fun q hq => hCsq q (hDC hq)),
    cofactorPoints_x_injective D a,?_,cofactorPoints_prime_hits D a (fun q hq => (hCsq q (hDC hq)).1),?_,?_⟩
  · exact rich_points_source_size C' P Uset a witness h s gamma S (sourceZ z) hg hS.le hZ hPpos
      hjSize hInv hjReward.le
  · exact rich_points_incidence (sourceY z) _ a delta _ S R (sourceZ z) cp gamma C' P Uset h hh s T
      hP hPpos (fun q hq => hCP q (hC'C hq)) htests
  · exact pointSlopes_thin (sourceY z) (sourceW z) Qplus R (Real.log z) qInitial bInitial a (delta/4)
      P Uset h s hW0 hR hPpos hUprime huLarge hpU hcost qRef (cofactorHit qRef a) hRefU

end ErdosInverseRefinement

end

end Erdos970

end OAI
