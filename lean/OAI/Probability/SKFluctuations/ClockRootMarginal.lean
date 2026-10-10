import Mathlib
import OAI.Probability.SKFluctuations.ReplicaProfileDifferentiation

namespace OAI

/-! Clock Root Marginal. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem markedAttach_preserves {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a)
    (q : ℕ → Fin (n+1) → ℝ≥0) (P : T.Assignment → ℝ) (x : Fin (n+1) → ℝ) :
    p.tree.expect w φ q (fun σ => P (p.restrict σ)) x = T.expect w φ q P x := by
  have hm : p.realize q ∈ (T.realize q).markedAttach a := by
    rw [← T.markedAttach_realize a q]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have h := (T.realize q).markedAttach_preserves hw φ (clockSteps_ordered ho q)
    (p.realize q) hm (fun σ => P ((T.assignmentEquiv q).symm σ)) x
  rw [p.tree.expect_realize,T.expect_realize]
  simpa only [MarkedPlacement.realize,Equiv.symm_apply_apply] using h

 theorem rootExpect_integrable {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (P : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    Integrable (fun y => T.expect w φ (fun j i => Real.toNNReal (q j i)) P (x+y))
      (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q₀ i))) := by
  have h := ((T.homTest P).eval_smooth hw φ ho q 0).integrable_zero_shift
    (ν := Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q₀ i))) x
  simpa only [ClockTree.eval_homTest] using h

 theorem rootExpect_mono {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    {P Q : T.Assignment → ℝ} (hPQ : ∀ σ, P σ ≤ Q σ)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ P q₀ q x ≤ T.rootExpect w φ Q q₀ q x := by
  rw [T.rootExpect_eq_integral,T.rootExpect_eq_integral]
  apply integral_mono (T.rootExpect_integrable hw φ ho P q₀ q x)
    (T.rootExpect_integrable hw φ ho Q q₀ q x)
  intro y
  dsimp only
  rw [T.expect_realize,T.expect_realize]
  exact (T.realize _).expect_mono hw φ (clockSteps_ordered ho _) (fun σ => hPQ _) _

omit [Nonempty S] in
 theorem rootExpect_const_mul (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (c : ℝ) (P : T.Assignment → ℝ)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ (fun σ => c*P σ) q₀ q x = c*T.rootExpect w φ P q₀ q x := by
  simp only [rootExpect_eq_integral,expect_realize,ReplicaTree.expect_const_mul,integral_const_mul]

 theorem rootExpect_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    {P : T.Assignment → ℝ} (hP : ∀ σ, 0 ≤ P σ)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    0 ≤ T.rootExpect w φ P q₀ q x := by
  rw [rootExpect_eq_integral]
  apply integral_nonneg
  intro y
  dsimp only
  rw [expect_realize]
  exact (T.realize _).expect_nonneg hw φ (clockSteps_ordered ho _) (fun σ => hP _) _

 theorem abs_rootExpect_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (P : T.Assignment → ℝ)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    |T.rootExpect w φ P q₀ q x| ≤ T.rootExpect w φ (fun σ => |P σ|) q₀ q x := by
  rw [rootExpect_eq_integral,rootExpect_eq_integral]
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono (T.rootExpect_integrable hw φ ho P q₀ q x).abs
    (T.rootExpect_integrable hw φ ho (fun σ => |P σ|) q₀ q x)
  intro y
  dsimp only
  rw [expect_realize,expect_realize]
  exact (T.realize _).abs_expect_le_expect_abs hw φ (clockSteps_ordered ho _) _ _

 theorem markedAttach_rootPreserves {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (P : T.Assignment → ℝ) (x : Fin (n+1) → ℝ) :
    p.tree.rootExpect w φ (fun σ => P (p.restrict σ)) q₀ q x = T.rootExpect w φ P q₀ q x := by
  simp only [rootExpect_eq_integral,T.markedAttach_preserves hw φ ho p hp]

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem profilePairTest_root_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (P : T.Assignment → ℝ)
    (K : ℕ → S → S → ℝ) {M : ℝ} (hK : ∀ j σ τ, |K j σ τ| ≤ M)
    (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    r.tree.rootExpect w φ (fun σ => |profilePairTest P K p r σ|) q₀ q x ≤
      M*T.rootExpect w φ (fun σ => |P σ|) q₀ q x := by
  calc
    _ ≤ r.tree.rootExpect w φ (fun σ => M*|P (p.restrict (r.restrict σ))|) q₀ q x := by
      apply r.tree.rootExpect_mono hw φ ho
      intro σ
      rw [profilePairTest,abs_mul,mul_comm M]
      exact mul_le_mul_of_nonneg_left (hK _ _ _) (abs_nonneg _)
    _ = _ := by
      rw [rootExpect_const_mul,p.tree.markedAttach_rootPreserves hw φ ho r hr q₀ q
        (fun τ => |P (p.restrict τ)|) x,
        T.markedAttach_rootPreserves hw φ ho p hp q₀ q (fun τ => |P τ|) x]

 

theorem rootProfileJets_relative_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ K ∈ Ks, ∀ j σ τ, |K j σ τ| ≤ M)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    |rootProfileJets w φ q₀ q x Ks T P| ≤
      jetVariation r Ks.length*T.rootExpect w φ (fun σ => |P σ|) q₀ q x*M^Ks.length := by
  induction Ks generalizing T r with
  | nil =>
    simpa only [rootProfileJets,jetVariation,List.length_nil,pow_zero,mul_one,one_mul] using
      T.abs_rootExpect_le hw φ ho P q₀ q x
  | cons K Ks ih =>
    let E := T.rootExpect w φ (fun σ => |P σ|) q₀ q x
    let D := jetVariation (r+2) Ks.length*(M*E)*M^Ks.length
    have hE : 0 ≤ E := T.rootExpect_nonneg hw φ ho (fun σ => abs_nonneg _) q₀ q x
    have hD : 0 ≤ D := mul_nonneg
      (mul_nonneg (jetVariation_nonneg _ _) (mul_nonneg hM hE)) (pow_nonneg hM _)
    have h := T.marked_pair_weight_abs_le ho hT
      (fun p s => rootProfileJets w φ q₀ q x Ks s.tree (profilePairTest P K p s)) hD
      (fun p hp s hs => by
        have hleaf : s.tree.leaves ≤ r+2 := by
          have h₁ := T.markedAttach_leaves 0 p hp
          have h₂ := p.tree.markedAttach_leaves 0 s hs
          omega
        apply (ih s.tree hleaf (profilePairTest P K p s)
          (fun L hL => hK L (List.mem_cons_of_mem _ hL))).trans
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM _)
        apply mul_le_mul_of_nonneg_left _ (jetVariation_nonneg _ _)
        exact T.profilePairTest_root_abs_le hw φ ho P K (hK K List.mem_cons_self) p hp s hs q₀ q x)
    apply h.trans_eq
    simp only [D,E,List.length_cons,jetVariation,pow_succ]
    ring

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped NNReal BigOperators
variable {S ι κ : Type*} [Fintype S] [Fintype ι] [Fintype κ]

 

def ClockTree.disorderProfileJets (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    List (ℕ → S → S → ℝ) → (T : ClockTree S as) → (T.Assignment → ℝ) → ℝ
  | [], T, P => T.disorderExpect w φ v q P x
  | K::Ks, T, P =>
    ((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun r => r.coeff*
        disorderProfileJets w φ v q x Ks r.tree (ClockTree.profilePairTest P K p r)).sum).sum/2

 theorem ClockTree.disorderProfileJets_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as) (P : T.Assignment → ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : κ → ℝ) :
    ClockTree.disorderProfileJets w (reindexFeature e φ) (fun i => v (e i))
      (fun j i => q j (e i)) x Ks T P =
      ClockTree.disorderProfileJets w φ v q (coordinateEquiv e x) Ks T P := by
  induction Ks generalizing T with
  | nil => exact T.disorderExpect_reindex e w φ v q P x
  | cons K Ks ih => simp only [disorderProfileJets,ih]

omit [Fintype S] in
 theorem ReplicaTree.coordinateProfile_reindex (e : κ ≃ ι)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : ℕ → ι → ℝ) :
    coordinateProfile (reindexFeature e φ) (fun j i => K j (e i)) = coordinateProfile φ K := by
  classical
  have he (σ : S) (i : κ) : reindexFeature e φ σ (Pi.single i 1) = φ σ (Pi.single (e i) 1) := by
    change φ σ (coordinateEquiv e (Pi.single i 1)) = _
    rw [coordinateEquiv_single]
  funext j σ τ
  simp only [coordinateProfile,he]
  exact e.sum_comp (fun i => K j i*φ σ (Pi.single i 1)*φ τ (Pi.single i 1))

variable [Nonempty S] {n : ℕ}

 theorem ClockTree.rootExpect_eq_disorderExpect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (P : T.Assignment → ℝ) (v : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ P (fun i => q 0 i-v i) (fun j i => q (j+1) i-q j i) x =
      T.disorderExpect w φ v q P x := by
  rw [← T.rootEval_testExpr hw φ ho]
  simp only [ClockTree.rootExpect,ClockTree.homTest,ClockTree.testExpr,
    ClockExpr.rootEval_homSum hw φ ho,ClockExpr.rootEval_listSum hw φ ho]

 theorem ClockTree.rootProfileJets_eq_disorderProfileJets {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    (P : T.Assignment → ℝ) (v : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ClockTree.rootProfileJets w φ (fun i => q 0 i-v i) (fun j i => q (j+1) i-q j i) x Ks T P =
      ClockTree.disorderProfileJets w φ v q x Ks T P := by
  induction Ks generalizing T with
  | nil => exact T.rootExpect_eq_disorderExpect hw φ ho P v q x
  | cons K Ks ih => simp only [rootProfileJets,disorderProfileJets,ih]

 theorem ClockTree.iteratedDeriv_disorderProfileJets {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (v : Fin (n+1) → ℝ)
    (q K : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+s*K j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, v i ≤ q 0 i+s*K 0 i)
    (P : T.Assignment → ℝ) (x : Fin (n+1) → ℝ) (k : ℕ) {t : ℝ} (ht : t ∈ Ioo l r) :
    iteratedDeriv k (fun s => T.disorderExpect w φ v (fun j i => q j i+s*K j i) P x) t =
      ClockTree.disorderProfileJets w φ v (fun j i => q j i+t*K j i) x
        (List.replicate k (ReplicaTree.coordinateProfile φ K)) T P := by
  have hinc : ∀ j, ∀ s ∈ Ioo l r, ∀ i,
      0 ≤ (q (j+1) i-q j i)+s*(K (j+1) i-K j i) := by
    intro j s hs i
    have h := hp s hs i (Nat.le_succ j)
    linarith
  have hroot : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q 0 i-v i+s*K 0 i := by
    intro s hs i
    linarith [hr s hs i]
  have h₀ (s : ℝ) : (fun i => q 0 i+s*K 0 i-v i) = fun i => q 0 i-v i+s*K 0 i := by
    funext i; ring
  have h₁ (s : ℝ) : (fun j i => (q (j+1) i+s*K (j+1) i)-(q j i+s*K j i)) =
      fun j i => q (j+1) i-q j i+s*(K (j+1) i-K j i) := by
    funext j i; ring
  have he (s : ℝ) : T.disorderExpect w φ v (fun j i => q j i+s*K j i) P x =
      T.rootExpect w φ P (fun i => q 0 i-v i+s*K 0 i)
        (fun j i => q (j+1) i-q j i+s*(K (j+1) i-K j i)) x := by
    rw [← T.rootExpect_eq_disorderExpect hw φ ho,h₀,h₁]
  simp only [he]
  rw [T.iteratedDeriv_rootProfileJets hw φ ho P _ _ K hinc hroot x k ht]
  rw [← T.rootProfileJets_eq_disorderProfileJets hw φ ho,h₀,h₁]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 

theorem ClockTree.iteratedDeriv_finiteProfileJets {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (v : ι → ℝ)
    (q K : ℕ → ι → ℝ) {l r : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+s*K j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, v i ≤ q 0 i+s*K 0 i)
    (P : T.Assignment → ℝ) (x : ι → ℝ) (k : ℕ) {t : ℝ} (ht : t ∈ Ioo l r) :
    iteratedDeriv k (fun s => T.disorderExpect w φ v (fun j i => q j i+s*K j i) P x) t =
      ClockTree.disorderProfileJets w φ v (fun j i => q j i+t*K j i) x
        (List.replicate k (ReplicaTree.coordinateProfile φ K)) T P := by
  let e := finiteJetEquiv ι
  have hd := T.iteratedDeriv_disorderProfileJets hw (reindexFeature e φ) ho
    (fun i => v (e i)) (fun j i => q j (e i)) (fun j i => K j (e i))
    (fun s hs i => hp s hs (e i)) (fun s hs i => hr s hs (e i)) P
    ((coordinateEquiv e).symm x) k ht
  have he (s : ℝ) : T.disorderExpect w (reindexFeature e φ) (fun i => v (e i))
      (fun j i => q j (e i)+s*K j (e i)) P ((coordinateEquiv e).symm x) =
      T.disorderExpect w φ v (fun j i => q j i+s*K j i) P x := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      T.disorderExpect_reindex e w φ v (fun j i => q j i+s*K j i) P ((coordinateEquiv e).symm x)
  simp only [he,ReplicaTree.coordinateProfile_reindex] at hd
  rw [T.disorderProfileJets_reindex e w φ _ P v (fun j i => q j i+t*K j i),
    ContinuousLinearEquiv.apply_symm_apply] at hd
  exact hd

 

theorem ClockTree.disorderProfileJets_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ) {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hP : ∀ σ, |P σ| ≤ C)
    (hK : ∀ K ∈ Ks, ∀ j σ τ, |K j σ τ| ≤ M)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    |ClockTree.disorderProfileJets w φ v q x Ks T P| ≤
      ClockTree.jetVariation r Ks.length*C*M^Ks.length := by
  let e := finiteJetEquiv ι
  have hd := ClockTree.rootProfileJets_abs_le hw (reindexFeature e φ) ho Ks T hT P hC hM hP hK
    (fun i => q 0 (e i)-v (e i)) (fun j i => q (j+1) (e i)-q j (e i))
    ((coordinateEquiv e).symm x)
  rw [T.rootProfileJets_eq_disorderProfileJets hw (reindexFeature e φ) ho Ks P
    (fun i => v (e i)) (fun j i => q j (e i)),
    T.disorderProfileJets_reindex e w φ Ks P v q,
    ContinuousLinearEquiv.apply_symm_apply] at hd
  exact hd

 
theorem ClockTree.disorderProfileJets_relative_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ K ∈ Ks, ∀ j σ τ, |K j σ τ| ≤ M)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    |ClockTree.disorderProfileJets w φ v q x Ks T P| ≤
      ClockTree.jetVariation r Ks.length*T.disorderExpect w φ v q (fun σ => |P σ|) x*M^Ks.length := by
  let e := finiteJetEquiv ι
  have hd := ClockTree.rootProfileJets_relative_abs_le hw (reindexFeature e φ) ho Ks T hT P hM hK
    (fun i => q 0 (e i)-v (e i)) (fun j i => q (j+1) (e i)-q j (e i))
    ((coordinateEquiv e).symm x)
  rw [T.rootProfileJets_eq_disorderProfileJets hw (reindexFeature e φ) ho Ks P
    (fun i => v (e i)) (fun j i => q j (e i)),
    T.rootExpect_eq_disorderExpect hw (reindexFeature e φ) ho (fun σ => |P σ|)
    (fun i => v (e i)) (fun j i => q j (e i)),
    T.disorderProfileJets_reindex e w φ Ks P v q,
    T.disorderExpect_reindex e w φ v q,
    ContinuousLinearEquiv.apply_symm_apply] at hd
  exact hd

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
theorem continuous_listSum {α : Type*} (L : List α) (f : α → ℝ → ℝ)
    (h : ∀ a ∈ L, Continuous (f a)) :
    Continuous (fun t => (L.map fun a => f a t).sum) := by
  induction L with
  | nil => exact continuous_const
  | cons a L ih =>
    exact (h a List.mem_cons_self).add
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 

theorem ClockTree.disorderExpect_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (v : ι → ℝ)
    (q : ℝ → ℕ → ι → ℝ) (hq : ∀ j, Continuous (fun t => q t j))
    (P : T.Assignment → ℝ) (x : ℝ → ι → ℝ) (hx : Continuous x) :
    Continuous (fun t => T.disorderExpect w φ v (q t) P (x t)) := by
  let e := finiteJetEquiv ι
  have h₀ : Continuous (fun t i => q t 0 (e i)-v (e i)) := by
    apply continuous_pi; intro i
    exact ((continuous_apply (e i)).comp (hq 0)).sub continuous_const
  have h₁ (j : ℕ) : Continuous (fun t i => q t (j+1) (e i)-q t j (e i)) := by
    apply continuous_pi; intro i
    exact ((continuous_apply (e i)).comp (hq (j+1))).sub
      ((continuous_apply (e i)).comp (hq j))
  have hd := (T.testExpr P).rootEval_continuous hw (reindexFeature e φ)
    (fun t i => q t 0 (e i)-v (e i))
    (fun j t i => q t (j+1) (e i)-q t j (e i)) h₀ h₁
    (fun t => (coordinateEquiv e).symm (x t)) ((coordinateEquiv e).symm.continuous.comp hx)
  have he (t : ℝ) : (T.testExpr P).rootEval w (reindexFeature e φ)
      (fun i => q t 0 (e i)-v (e i))
      (fun j i => q t (j+1) (e i)-q t j (e i)) ((coordinateEquiv e).symm (x t)) =
      T.disorderExpect w φ v (q t) P (x t) := by
    rw [T.rootEval_testExpr hw (reindexFeature e φ) ho (fun i => v (e i))
      (fun j i => q t j (e i)),T.disorderExpect_reindex e w φ v (q t),
      ContinuousLinearEquiv.apply_symm_apply]
  simpa only [he] using hd

 

theorem ClockTree.disorderProfileJets_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℝ → ℕ → ι → ℝ)
    (hq : ∀ j, Continuous (fun t => q t j)) (x : ℝ → ι → ℝ) (hx : Continuous x)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as) (P : T.Assignment → ℝ) :
    Continuous (fun t => ClockTree.disorderProfileJets w φ v (q t) (x t) Ks T P) := by
  induction Ks generalizing T with
  | nil => exact T.disorderExpect_continuous hw φ ho v q hq P x hx
  | cons K Ks ih =>
    simp only [disorderProfileJets]
    apply Continuous.div_const
    apply continuous_listSum
    intro p hp
    apply Continuous.const_mul
    apply continuous_listSum
    intro r hr
    exact (ih r.tree (ClockTree.profilePairTest P K p r)).const_mul r.coeff

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 

theorem ClockTree.hasDerivAt_finiteProfileJets {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q K : ℕ → ι → ℝ) {l r : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+s*K j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, v i ≤ q 0 i+s*K 0 i)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as) (P : T.Assignment → ℝ)
    (x : ι → ℝ) {t : ℝ} (ht : t ∈ Ioo l r) :
    HasDerivAt (fun s => ClockTree.disorderProfileJets w φ v (fun j i => q j i+s*K j i) x Ks T P)
      (ClockTree.disorderProfileJets w φ v (fun j i => q j i+t*K j i) x
        (Ks++[ReplicaTree.coordinateProfile φ K]) T P) t := by
  induction Ks generalizing T with
  | nil =>
    have hd := T.hasDerivAt_finiteDisorderExpect hw φ v q K hp hr P ht x
    have he := T.iteratedDeriv_finiteProfileJets hw φ ho v q K hp hr P x 1 ht
    simp only [iteratedDeriv_one] at he
    rw [hd.deriv] at he
    exact he ▸ hd
  | cons L Ks ih =>
    exact (hasDerivAt_listSum (T.markedAttach 0) _ _ (fun p _ =>
      (hasDerivAt_listSum (p.tree.markedAttach 0) _ _ (fun r _ =>
        (ih r.tree (ClockTree.profilePairTest P L p r)).const_mul r.coeff)).const_mul p.coeff)).div_const 2

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators

section
variable (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
  {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
  (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ)
  (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
  (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
  (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
include hq0 hq hb hh hK hbm hhm hKm ho

 theorem cutLowJet_eq_iteratedDeriv (k : ℕ) {l t : ℝ}
    (hl : l ∈ Ioo (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    iteratedDeriv k (fun s => T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U s t b h K) P x) l = cutLowJet n q U b h K T P x k l t := by
  induction k generalizing l with
  | zero => exact (cutLowJet_zero n q U b h K T ho P x l t).symm
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun s => T.disorderExpect (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U s t b h K) P x) =ᶠ[𝓝 l]
        (fun s => cutLowJet n q U b h K T P x k s t) := by
      filter_upwards [isOpen_Ioo.mem_nhds hl] with s hs
      exact ih hs
    rw [he.deriv_eq]
    exact (cutLowJet_hasDerivAt_l n q U hl ht b h K hq0 hq hb hh hK hbm hhm hKm T ho P x k).deriv

 

theorem cutLowJet_eq_profileJets (k : ℕ) {l t : ℝ}
    (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    cutLowJet n q U b h K T P x k l t =
      ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l t b h K) x
        (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K))) T P := by
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
      cutLBase n q U t b h K 0 i+s*cutLSlope n U t b h K 0 i := by
    intro s hs i
    have hn := cutFullVariance_nonneg n q U (l := s) ⟨hs.1.le,hs.2.le⟩ ht hq0 hb hh hK 0 i
    simpa only [cutFullVariance_l_affine,Pi.zero_apply] using hn
  have hi : Set.EqOn (fun l => cutLowJet n q U b h K T P x k l t)
      (fun l => ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
        (cutFullVariance n q U l t b h K) x
        (List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K))) T P)
      (Ioo (0:ℝ) 1) := by
    intro s hs
    dsimp only
    rw [← cutLowJet_eq_iteratedDeriv n q U b h K T ho P x hq0 hq hb hh hK hbm hhm hKm k hs ht]
    simpa only [cutFullVariance_l_affine] using
      T.iteratedDeriv_finiteProfileJets (fullWeight_pos n) (fullFeature n) ho 0
        (cutLBase n q U t b h K) (cutLSlope n U t b h K)
        (cutL_affine_monotone n q U ht hq hb hh hK hbm hhm hKm) hr P x k hs
  have hc := hi.closure (cutLowJet_continuous_l n q U b h K T P x k t)
    (ClockTree.disorderProfileJets_continuous (fullWeight_pos n) (fullFeature n) ho 0
      (fun l => cutFullVariance n q U l t b h K) (cutFullVariance_continuous_l n q U b h K t)
      (fun _ => x) continuous_const _ T P)
  apply hc
  simpa only [closure_Ioo (show (0:ℝ) ≠ 1 by norm_num)] using hl

end
end SKFluctuations.Cavity

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Fintype ι]

theorem expect_fork (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T U : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (P : (T.fork U).Assignment → ℝ) (x : ι → ℝ) :
    (T.fork U).expect w φ q P x =
      T.expect w φ q (fun σ => U.expect w φ q (fun τ => P (σ,τ)) x) x := by
  simp only [expect,weight_fork,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

variable [Nonempty S]

theorem expect_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (b : PositiveMass)
    (T : ClockTree S as) (ho : MassOrdered b.val as) (q : ℕ → ι → ℝ≥0)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    (T.step b).expect w φ q P x =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
        (T.expect w φ (fun j => q (j+1)) P) x := by
  rw [expect_realize]
  change ((T.realize (fun j => q (j+1))).step (b.val,q 0)).expect w φ
    (fun σ => P ((T.assignmentEquiv (fun j => q (j+1))).symm σ)) x = _
  rw [ReplicaTree.expect_step hw φ _ b.val (q 0) (clockSteps_ordered ho _)]
  congr 1
  funext y
  exact (T.expect_realize w φ _ P y).symm

theorem expect_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (c : ℝ) (x : ι → ℝ) : T.expect w φ q (fun _ => c) x = c := by
  rw [expect_realize]
  exact (T.realize q).expect_const hw φ (clockSteps_ordered ho q) c x

 
def singleMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (as : List PositiveMass) (q : ℕ → ι → ℝ≥0) (P : S → ℝ) (x : ι → ℝ) : ℝ :=
  (single as).expect w φ q (fun σ => P (singleEquiv (S:=S) as σ)) x

theorem singleMean_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (b : PositiveMass)
    (ho : MassOrdered b.val as) (q : ℕ → ι → ℝ≥0) (P : S → ℝ) (x : ι → ℝ) :
    singleMean w φ (b::as) q P x =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
        (singleMean w φ as (fun j => q (j+1)) P) x := by
  exact expect_step hw φ b (single as) ho q _ x

 

theorem expect_atSlot {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (s : T.Slot) (P : S → ℝ) (x : ι → ℝ) :
    T.expect w φ q (fun σ => P (T.atSlot σ s)) x = singleMean w φ as q P x := by
  induction T generalizing a q P x with
  | leaf => rfl
  | step b T ih =>
    rw [expect_step hw φ b T ho.2.2,singleMean_step hw φ b ho.2.2]
    congr 1
    funext y
    exact ih ho.2.2 _ s P y
  | fork T U ihT ihU =>
    cases s with
    | inl s =>
      rw [expect_fork]
      change T.expect w φ q (fun σ => U.expect w φ q (fun _ => P (T.atSlot σ s)) x) x = _
      simp only [U.expect_const hw φ ho q]
      exact ihT ho q s P x
    | inr s =>
      rw [expect_fork]
      change T.expect w φ q (fun _ => U.expect w φ q (fun σ => P (U.atSlot σ s)) x) x = _
      rw [T.expect_const hw φ ho q]
      exact ihU ho q s P x

end SKFluctuations.Hierarchy.ClockTree

end

end OAI
