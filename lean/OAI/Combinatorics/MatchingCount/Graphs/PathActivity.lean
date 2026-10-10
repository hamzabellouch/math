import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.FirstHoleSortedCons
import OAI.Combinatorics.MatchingCount.Graphs.Vertex

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open Finset

variable {V E : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]

instance vertexLinearOrder (m : ℕ) : LinearOrder (Vertex V E m) := by
  letI : LinearOrder (E × Fin m) := LinearOrder.lift' (toLex : E × Fin m → E ×ₗ Fin m) (fun _ _ h => h)
  exact LinearOrder.lift' (toLex : V ⊕ (E × Fin m) → V ⊕ₗ (E × Fin m)) (fun _ _ h => h)

omit [Fintype V] [Fintype E] in
@[simp] lemma terminal_lt_iff (m : ℕ) (a b : V) :
    @LT.lt (Vertex V E m) (vertexLinearOrder (V := V) (E := E) m).toLT (Sum.inl a) (Sum.inl b) ↔ a < b := by
  change Sum.Lex (· < · : V → V → Prop) _ (Sum.inl a) (Sum.inl b) ↔ a < b
  exact Sum.lex_inl_inl

omit [Fintype V] in
lemma real_threshold_eq [Fintype V] (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (t : E → Fin (m+1) → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    thresholdGraph (activity u v m t) τ=realThreshold u v m t τ := by
  ext a b
  rw [realThreshold_adj_iff u v m hm t τ hτ]
  change (a ≠ b ∧ τ ≤ edgeActivity (activity u v m t) a b) ↔ _
  rw [edgeActivity_of_symmetric _ (activity_symm u v m t)]

theorem interval_le_bottleneck (u v : E → V) (m : ℕ) (hm : 2 ≤ m)
    (huv : ∀ e, u e ≠ v e) (t : E → Fin (m+1) → ℝ) (e : E)
    (i j : Fin (m+2)) (hij : i.val < j.val) (T : ℝ)
    (ht : ∀ k : Fin (m+1), i.val ≤ k.val → k.val < j.val → T ≤ t e k) :
    T ≤ bottleneck (activity u v m t) (atVertex u v m e i) (atVertex u v m e j) := by
  by_cases hT : 1 < T
  · apply (bottleneck_threshold _ _ _ ?_ T hT).mpr
    · rw [real_threshold_eq u v m hm t T (by linarith)]
      exact path_interval_reachable u v m t T e i j hij.le ht
    · intro he
      have := congrArg Fin.val (atVertex_injective u v m e (huv e) he)
      omega
  · exact (le_of_not_gt hT).trans (one_le_bottleneck _ _ _)

noncomputable def pathActivity (p : ℕ) (B Hu Hv lam : E → ℝ) : E → Fin (4*p+1) → ℝ :=
  fun e => profileActivity p (B e) (Hu e) (Hv e) (lam e)

noncomputable def realBottleneck (u v : E → V) (p : ℕ) (B Hu Hv lam : E → ℝ) :
    Vertex V E (4*p) → Vertex V E (4*p) → ℝ :=
  bottleneck (activity u v (4*p) (pathActivity p B Hu Hv lam))

theorem realBottleneck_internal_cap (u v : E → V) (p : ℕ) (hp : 1 ≤ p)
    (B Hu Hv lam : E → ℝ) (hB : ∀ e, 1 ≤ B e) (hHu : ∀ e, 0 ≤ Hu e)
    (hHv : ∀ e, 0 ≤ Hv e) (hlam : ∀ e, lam e ≤ B e) (e : E) (j : Fin (4*p))
    (a : Vertex V E (4*p)) :
    realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) a ≤
      internalStrength p (B e) (Hu e) (Hv e) j := by
  apply bottleneck_le_row_bound
  · exact (hB e).trans (le_internalStrength _ _ _ _ _)
  · intro b hb
    rw [edgeActivity_of_symmetric _ (activity_symm _ _ _ _)]
    apply internal_activity_le u v (4*p) (by omega)
    · exact (zero_le_one.trans (hB e)).trans (le_internalStrength _ _ _ _ _)
    · exact (internalStrength_incident p (B e) (Hu e) (Hv e) (lam e)
        (hHu e) (hHv e) (hlam e) j).1
    · exact (internalStrength_incident p (B e) (Hu e) (Hv e) (lam e)
        (hHu e) (hHv e) (hlam e) j).2

theorem realBottleneck_left_home (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hHu : ∀ e, 0 ≤ Hu e)
    (e : E) (j : Fin (4*p)) (hj : j.val < 2*p) :
    internalStrength p (B e) (Hu e) (Hv e) j ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inl (u e)) := by
  rw [realBottleneck,bottleneck_comm]
  have h := interval_le_bottleneck u v (4*p) (by omega) huv
    (pathActivity p B Hu Hv lam) e 0 j.succ.castSucc (by simp) _
    (fun k _ hk => internalStrength_left_leg p (B e) (Hu e) (Hv e) (lam e)
      (hHu e) j hj k (by simp only [Fin.val_castSucc,Fin.val_succ] at hk; omega))
  simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h

 theorem realBottleneck_right_home (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hHv : ∀ e, 0 ≤ Hv e)
    (e : E) (j : Fin (4*p)) (hj : ¬ j.val < 2*p) :
    internalStrength p (B e) (Hu e) (Hv e) j ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inl (v e)) := by
  have h := interval_le_bottleneck u v (4*p) (by omega) huv
    (pathActivity p B Hu Hv lam) e j.succ.castSucc (Fin.last (4*p+1))
    (by simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_last]; omega) _
    (fun k hk _ => internalStrength_right_leg p (B e) (Hu e) (Hv e) (lam e)
      (hHv e) j hj k (by simpa only [Fin.val_castSucc,Fin.val_succ] using hk))
  simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h

theorem realBottleneck_path_lower (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hlam : ∀ e, lam e ≤ B e)
    (e : E) (i j : Fin (4*p+2)) :
    lam e ≤ realBottleneck u v p B Hu Hv lam (atVertex u v (4*p) e i)
      (atVertex u v (4*p) e j) ∨ i=j := by
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · left
    exact interval_le_bottleneck u v (4*p) (by omega) huv (pathActivity p B Hu Hv lam) e i j hij _
      (fun k _ _ => profile_lower p (B e) (Hu e) (Hv e) (lam e) (hlam e) k)
  · exact Or.inr (Fin.ext hij)
  · left
    rw [realBottleneck,bottleneck_comm]
    exact interval_le_bottleneck u v (4*p) (by omega) huv (pathActivity p B Hu Hv lam) e j i hij _
      (fun k _ _ => profile_lower p (B e) (Hu e) (Hv e) (lam e) (hlam e) k)

noncomputable def leftFactor (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p)) : ℝ :=
  if j.val < 2*p then 1 else lam / internalStrength p B Hu Hv j

noncomputable def rightFactor (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p)) : ℝ :=
  if j.val < 2*p then lam / internalStrength p B Hu Hv j else 1

noncomputable def neutralFactor (p : ℕ) (B Hu Hv lam : ℝ) (j k : Fin (4*p)) : ℝ :=
  if k.val < 2*p then (internalStrength p B Hu Hv j)⁻¹
  else if j.val < 2*p then lam / (internalStrength p B Hu Hv j * internalStrength p B Hu Hv k)
  else (internalStrength p B Hu Hv k)⁻¹

lemma leftFactor_eq_potential (p : ℕ) (B Hu Hv lam : ℝ) (j : Fin (4*p))
    (hj : j.val%2=1) :
    leftFactor p B Hu Hv lam j = (vertexPotential p B Hu Hv lam (j.val+1))⁻¹ := by
  rw [consumed_left_potential p B Hu Hv lam j hj]
  unfold leftFactor
  split_ifs <;> simp

lemma rightFactor_eq_potential (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≠ 0)
    (j : Fin (4*p)) (hj : j.val%2=0) :
    rightFactor p B Hu Hv lam j = lam / vertexPotential p B Hu Hv lam (j.val+1) := by
  rw [consumed_right_potential p B Hu Hv lam j hj]
  unfold rightFactor
  split_ifs <;> simp [hlam]

lemma neutralFactor_eq_potential (p : ℕ) (B Hu Hv lam : ℝ) (hlam : lam ≠ 0)
    (j k : Fin (4*p)) (hjk : j.val < k.val) (hj : j.val%2=0) (hk : k.val%2=1) :
    neutralFactor p B Hu Hv lam j k =
      (vertexPotential p B Hu Hv lam (j.val+1) * vertexPotential p B Hu Hv lam (k.val+1))⁻¹ := by
  rw [consumed_right_potential p B Hu Hv lam j hj,consumed_left_potential p B Hu Hv lam k hk]
  unfold neutralFactor
  by_cases hk' : k.val < 2*p
  · have hj' : j.val < 2*p := by omega
    simp [hk',hj']
  · by_cases hj' : j.val < 2*p
    · simp [hk',hj',div_eq_mul_inv,mul_inv_rev,inv_inv]
      ring
    · simp only [ite_eq_right hk',ite_eq_right hj']
      have he : lam * (internalStrength p B Hu Hv k / lam) = internalStrength p B Hu Hv k := by
        field_simp [hlam]
      rw [he]

lemma leftFactor_nonneg (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 ≤ lam)
    (j : Fin (4*p)) : 0 ≤ leftFactor p B Hu Hv lam j := by
  unfold leftFactor
  split_ifs
  · norm_num
  · exact div_nonneg hlam ((hB.trans_le (le_internalStrength _ _ _ _ _)).le)

lemma rightFactor_nonneg (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 ≤ lam)
    (j : Fin (4*p)) : 0 ≤ rightFactor p B Hu Hv lam j := by
  unfold rightFactor
  split_ifs
  · exact div_nonneg hlam ((hB.trans_le (le_internalStrength _ _ _ _ _)).le)
  · norm_num

lemma neutralFactor_nonneg (p : ℕ) (B Hu Hv lam : ℝ) (hB : 0 < B) (hlam : 0 ≤ lam)
    (j k : Fin (4*p)) : 0 ≤ neutralFactor p B Hu Hv lam j k := by
  have hj := (hB.trans_le (le_internalStrength p B Hu Hv j)).le
  have hk := (hB.trans_le (le_internalStrength p B Hu Hv k)).le
  unfold neutralFactor
  split_ifs
  · exact inv_nonneg.mpr hj
  · exact div_nonneg hlam (mul_nonneg hj hk)
  · exact inv_nonneg.mpr hk

theorem neutral_local_charge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e)
    (hHu : ∀ e, 0 ≤ Hu e) (hHv : ∀ e, 0 ≤ Hv e) (hlam : ∀ e, lam e ≤ B e)
    (e : E) (j k : Fin (4*p)) (hjk : j.val < k.val) :
    neutralFactor p (B e) (Hu e) (Hv e) (lam e) j k *
      internalStrength p (B e) (Hu e) (Hv e) j * internalStrength p (B e) (Hu e) (Hv e) k ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inr (e,k)) := by
  have hj0 := hB e |>.trans_le (le_internalStrength p (B e) (Hu e) (Hv e) j)
  have hk0 := hB e |>.trans_le (le_internalStrength p (B e) (Hu e) (Hv e) k)
  unfold neutralFactor
  by_cases hk : k.val < 2*p
  · rw [ite_eq_left hk,inv_mul_cancel₀ hj0.ne',one_mul]
    have h := interval_le_bottleneck u v (4*p) (by omega) huv
      (pathActivity p B Hu Hv lam) e j.succ.castSucc k.succ.castSucc
      (by simpa only [Fin.val_castSucc,Fin.val_succ,Nat.add_lt_add_iff_right] using hjk) _
      (fun i _ hi => internalStrength_left_leg p (B e) (Hu e) (Hv e) (lam e)
        (hHu e) k hk i (by simp only [Fin.val_castSucc,Fin.val_succ] at hi; omega))
    simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h
  · rw [ite_eq_right hk]
    by_cases hj : j.val < 2*p
    · rw [ite_eq_left hj]
      have heq : lam e / (internalStrength p (B e) (Hu e) (Hv e) j *
          internalStrength p (B e) (Hu e) (Hv e) k) *
          internalStrength p (B e) (Hu e) (Hv e) j * internalStrength p (B e) (Hu e) (Hv e) k=lam e := by
        field_simp [hj0.ne',hk0.ne']
      rw [heq]
      have h := interval_le_bottleneck u v (4*p) (by omega) huv
        (pathActivity p B Hu Hv lam) e j.succ.castSucc k.succ.castSucc
        (by simpa only [Fin.val_castSucc,Fin.val_succ,Nat.add_lt_add_iff_right] using hjk) _
        (fun i _ _ => profile_lower p (B e) (Hu e) (Hv e) (lam e) (hlam e) i)
      simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h
    · rw [ite_eq_right hj]
      have heq : (internalStrength p (B e) (Hu e) (Hv e) k)⁻¹ *
          internalStrength p (B e) (Hu e) (Hv e) j * internalStrength p (B e) (Hu e) (Hv e) k=
          internalStrength p (B e) (Hu e) (Hv e) j := by field_simp [hk0.ne']
      rw [heq]
      have h := interval_le_bottleneck u v (4*p) (by omega) huv
        (pathActivity p B Hu Hv lam) e j.succ.castSucc k.succ.castSucc
        (by simpa only [Fin.val_castSucc,Fin.val_succ,Nat.add_lt_add_iff_right] using hjk) _
        (fun i hi _ => internalStrength_right_leg p (B e) (Hu e) (Hv e) (lam e)
          (hHv e) j hj i (by simpa only [Fin.val_castSucc,Fin.val_succ] using hi))
      simpa only [atVertex_zero,atVertex_internal,atVertex_last,realBottleneck] using h

theorem left_local_charge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e)
    (hHu : ∀ e, 0 ≤ Hu e) (hlam : ∀ e, lam e ≤ B e) (e : E) (j : Fin (4*p)) :
    leftFactor p (B e) (Hu e) (Hv e) (lam e) j * internalStrength p (B e) (Hu e) (Hv e) j ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inl (u e)) := by
  have hj0 := hB e |>.trans_le (le_internalStrength p (B e) (Hu e) (Hv e) j)
  unfold leftFactor
  by_cases hj : j.val < 2*p
  · rw [ite_eq_left hj,one_mul]
    exact realBottleneck_left_home u v huv p hp B Hu Hv lam hHu e j hj
  · rw [ite_eq_right hj,div_mul_cancel₀ _ hj0.ne']
    rw [realBottleneck,bottleneck_comm]
    have h := interval_le_bottleneck u v (4*p) (by omega) huv
      (pathActivity p B Hu Hv lam) e 0 j.succ.castSucc (by simp) _
      (fun i _ _ => profile_lower p (B e) (Hu e) (Hv e) (lam e) (hlam e) i)
    simpa only [atVertex_zero,atVertex_internal] using h

theorem right_local_charge (u v : E → V) (huv : ∀ e, u e ≠ v e)
    (p : ℕ) (hp : 1 ≤ p) (B Hu Hv lam : E → ℝ) (hB : ∀ e, 0 < B e)
    (hHv : ∀ e, 0 ≤ Hv e) (hlam : ∀ e, lam e ≤ B e) (e : E) (j : Fin (4*p)) :
    rightFactor p (B e) (Hu e) (Hv e) (lam e) j * internalStrength p (B e) (Hu e) (Hv e) j ≤
      realBottleneck u v p B Hu Hv lam (Sum.inr (e,j)) (Sum.inl (v e)) := by
  have hj0 := hB e |>.trans_le (le_internalStrength p (B e) (Hu e) (Hv e) j)
  unfold rightFactor
  by_cases hj : j.val < 2*p
  · rw [ite_eq_left hj,div_mul_cancel₀ _ hj0.ne']
    have h := interval_le_bottleneck u v (4*p) (by omega) huv
      (pathActivity p B Hu Hv lam) e j.succ.castSucc (Fin.last (4*p+1))
      (by simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_last]; omega) _
      (fun i _ _ => profile_lower p (B e) (Hu e) (Hv e) (lam e) (hlam e) i)
    simpa only [atVertex_internal,atVertex_last,realBottleneck] using h
  · rw [ite_eq_right hj,one_mul]
    exact realBottleneck_right_home u v huv p hp B Hu Hv lam hHv e j hj

abbrev LogicalEdge (V : Type*) [LinearOrder V] := {q : V × V // q.1 < q.2}

instance logicalEdgeLinearOrder : LinearOrder (LogicalEdge V) :=
  LinearOrder.lift' (fun e => toLex e.val) (fun _ _ h => Subtype.ext h)

def source (e : LogicalEdge V) : V := e.val.1

def target (e : LogicalEdge V) : V := e.val.2

omit [Fintype V] in
lemma source_ne_target [Fintype V] (e : LogicalEdge V) : source e ≠ target e := e.property.ne

def logicalActivity (w : V → V → ℝ) (e : LogicalEdge V) : ℝ :=
  edgeActivity w (source e) (target e)

omit [Fintype V] in
lemma logical_threshold_eq [Fintype V] (w : V → V → ℝ) (τ : ℝ) :
    logicalThreshold source target (logicalActivity w) τ=thresholdGraph w τ := by
  ext a b
  change (a ≠ b ∧ ∃ e : LogicalEdge V, s(source e,target e)=s(a,b) ∧ τ ≤ logicalActivity w e) ↔
    (a ≠ b ∧ τ ≤ edgeActivity w a b)
  constructor
  · rintro ⟨hne,e,he,ht⟩
    refine ⟨hne,?_⟩
    rcases Sym2.eq_iff.mp he with he | he
    · simpa only [logicalActivity,he.1,he.2] using ht
    · simpa only [logicalActivity,he.1,he.2,edgeActivity_comm w b a] using ht
  · rintro ⟨hne,ht⟩
    refine ⟨hne,?_⟩
    rcases lt_or_gt_of_ne hne with hab | hab
    · exact ⟨⟨(a,b),hab⟩,rfl,ht⟩
    · exact ⟨⟨(b,a),hab⟩,Sym2.eq_swap,by simpa [logicalActivity,source,target,edgeActivity_comm w b a] using ht⟩

theorem terminal_bottleneck (w : V → V → ℝ) (p : ℕ) (hp : 1 ≤ p)
    (Hu Hv : LogicalEdge V → ℝ) (a b : V) :
    realBottleneck source target p (fun e => bottleneck w (source e) (target e))
      Hu Hv (logicalActivity w) (Sum.inl a) (Sum.inl b) = bottleneck w a b := by
  by_cases hab : a=b
  · subst b; simp [realBottleneck,bottleneck]
  apply bottleneck_eq_of_threshold_iff _ w _ _ a b (Sum.inl_injective.ne hab) hab
  intro τ hτ
  rw [real_threshold_eq source target (4*p) (by omega) _ τ (by linarith)]
  rw [terminal_threshold_iff source target (4*p) ⟨2*p,by omega⟩
    (logicalActivity w) (pathActivity p (fun e => bottleneck w (source e) (target e)) Hu Hv (logicalActivity w))
    (fun e => profile_center p _ _ _ _) ?_ τ a b]
  · rw [logical_threshold_eq]
  · intro e i
    exact profile_lower p _ _ _ _ (edgeActivity_le_bottleneck w (source e) (target e)
      (source_ne_target e)) i

noncomputable def enlargedHoles (m : ℕ) (R₀ : Finset V) (U : E → Finset (Fin m)) :
    Finset (Vertex V E m) :=
  R₀.map ⟨Sum.inl,Sum.inl_injective⟩ ∪
    Finset.univ.biUnion (fun e => (U e).map ⟨fun j => Sum.inr (e,j),fun _ _ h => congrArg Prod.snd (Sum.inr_injective h)⟩)

omit [Fintype V] in
@[simp] lemma mem_enlargedHoles_left [Fintype V] (m : ℕ) (R₀ : Finset V) (U : E → Finset (Fin m)) (x : V) :
    Sum.inl x ∈ enlargedHoles m R₀ U ↔ x ∈ R₀ := by
  classical
  simp [enlargedHoles]

omit [Fintype V] in
@[simp] lemma mem_enlargedHoles_right [Fintype V] (m : ℕ) (R₀ : Finset V) (U : E → Finset (Fin m))
    (e : E) (j : Fin m) : Sum.inr (e,j) ∈ enlargedHoles m R₀ U ↔ j ∈ U e := by
  classical
  simp only [enlargedHoles,Finset.mem_union,Finset.mem_map,Finset.mem_biUnion,
    Finset.mem_univ,true_and]
  constructor
  · rintro (⟨x,hx,hxx⟩ | ⟨e',j',hj,hjj⟩)
    · change (Sum.inl x : Vertex V E m)=Sum.inr (e,j) at hxx
      cases hxx
    · have hh := Prod.mk.inj (Sum.inr_injective hjj)
      rcases hh with ⟨hee,hjj⟩
      subst e'; subst j'; exact hj
  · intro hj; exact Or.inr ⟨e,j,hj,rfl⟩

noncomputable def neutralPairs (m : ℕ) (d : E → HoleBlocks m) :
    List (Vertex V E m × Vertex V E m) :=
  Finset.univ.toList.flatMap (fun e => (d e).neutral.map
    (fun q => (Sum.inr (e,q.1),Sum.inr (e,q.2))))

noncomputable def consumedPairs (u v : E → V) (m : ℕ) (d : E → HoleBlocks m) :
    List (Vertex V E m × Vertex V E m) :=
  Finset.univ.toList.flatMap (fun e =>
    (d e).left.toList.map (fun j => (Sum.inr (e,j),Sum.inl (u e))) ++
    (d e).right.toList.map (fun j => (Sum.inr (e,j),Sum.inl (v e))))

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
lemma tagged_nodup [Fintype V] [LinearOrder V] [LinearOrder E]
    {m : ℕ} (xs : E → List (Fin m)) (hx : ∀ e, (xs e).Nodup) :
    (Finset.univ.toList.flatMap (fun e => (xs e).map (fun j => (Sum.inr (e,j) : Vertex V E m)))).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun e _ => (hx e).map (fun _ _ h => congrArg Prod.snd (Sum.inr_injective h)),?_⟩
  apply (Finset.nodup_toList _).imp
  intro e e' hne
  apply List.disjoint_left.mpr
  intro a ha ha'
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j',hj',he⟩ := List.mem_map.mp ha'
  exact hne (congrArg Prod.fst (Sum.inr_injective he)).symm

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
lemma pairVertices_neutral [Fintype V] [LinearOrder V] [LinearOrder E]
    (m : ℕ) (d : E → HoleBlocks m) :
    pairVertices (neutralPairs (V := V) m d)=
      Finset.univ.toList.flatMap (fun e =>
        ((d e).neutral.flatMap (fun q => [q.1,q.2])).map (fun j => Sum.inr (e,j))) := by
  simp [pairVertices,neutralPairs,List.flatMap_assoc,List.flatMap_map,List.map_flatMap]

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
lemma consumed_sources [Fintype V] [LinearOrder V] [LinearOrder E]
    (u v : E → V) (m : ℕ) (d : E → HoleBlocks m) :
    (consumedPairs u v m d).map Prod.fst=
      Finset.univ.toList.flatMap (fun e =>
        ((d e).left.toList++(d e).right.toList).map (fun j => Sum.inr (e,j))) := by
  simp [consumedPairs,List.map_flatMap,List.map_append,List.map_map,Function.comp_def]

theorem source_lists_nodup {m : ℕ} (u v : E → V) (U : E → Finset (Fin m))
    (d : E → HoleBlocks m) (he : ∀ e, (d e).flatten=(U e).sort (· ≤ ·)) :
    (pairVertices (neutralPairs (V := V) m d) ++ (consumedPairs u v m d).map Prod.fst).Nodup := by
  rw [pairVertices_neutral,consumed_sources]
  apply List.nodup_append.mpr
  refine ⟨tagged_nodup _ (fun e => (List.nodup_append.mp ((d e).reordered_nodup (he e))).1),
    tagged_nodup _ (fun e => (List.nodup_append.mp ((d e).reordered_nodup (he e))).2.1),?_⟩
  intro a ha b hb hab
  subst b
  obtain ⟨e,he',ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
  obtain ⟨e',he'',hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨j',hj',heq⟩ := List.mem_map.mp hb
  have heq' := Sum.inr_injective heq
  cases heq'
  exact (List.nodup_append.mp ((d e).reordered_nodup (he e))).2.2 j hj j hj' rfl

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
@[simp] lemma mem_neutralPairs [Fintype V] [LinearOrder V] [LinearOrder E]
    {m : ℕ} (d : E → HoleBlocks m) (q : Vertex V E m × Vertex V E m) :
    q ∈ neutralPairs m d ↔ ∃ e r, r ∈ (d e).neutral ∧ q=(Sum.inr (e,r.1),Sum.inr (e,r.2)) := by
  classical
  simp only [neutralPairs,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,List.mem_map]
  constructor
  · rintro ⟨e,r,hr,he⟩; exact ⟨e,r,hr,he.symm⟩
  · rintro ⟨e,r,hr,rfl⟩; exact ⟨e,r,hr,rfl⟩

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
@[simp] lemma mem_consumedPairs [Fintype V] [LinearOrder V] [LinearOrder E]
    {m : ℕ} (u v : E → V) (d : E → HoleBlocks m)
    (q : Vertex V E m × Vertex V E m) :
    q ∈ consumedPairs u v m d ↔ ∃ e j,
      (j ∈ (d e).left ∧ q=(Sum.inr (e,j),Sum.inl (u e))) ∨
      (j ∈ (d e).right ∧ q=(Sum.inr (e,j),Sum.inl (v e))) := by
  classical
  simp only [consumedPairs,List.mem_flatMap,Finset.mem_toList,Finset.mem_univ,true_and,
    List.mem_append,List.mem_map,Option.mem_toList]
  constructor
  · rintro ⟨e,h | h⟩
    · obtain ⟨j,hj,he⟩ := h; exact ⟨e,j,Or.inl ⟨hj,he.symm⟩⟩
    · obtain ⟨j,hj,he⟩ := h; exact ⟨e,j,Or.inr ⟨hj,he.symm⟩⟩
  · rintro ⟨e,j,h | h⟩
    · exact ⟨e,Or.inl ⟨j,h.1,h.2.symm⟩⟩
    · exact ⟨e,Or.inr ⟨j,h.1,h.2.symm⟩⟩

end MatchingFPRAS.Enlargement

end OAI
