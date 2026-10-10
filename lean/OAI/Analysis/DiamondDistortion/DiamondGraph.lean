import OAI.Analysis.DiamondDistortion.ForestModels

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Diamond

/-- Stage edges, retaining their parent, child number, and side. -/
@[reducible] def Edge : ℕ → Type
  | 0 => Unit
  | n + 1 => Edge n × ℕ × Bool

/-- At every replacement every parent edge receives countably many distinct new vertices. -/
@[reducible] def Vertex : ℕ → Type
  | 0 => Bool
  | n + 1 => Vertex n ⊕ (Edge n × ℕ)

def endpoint : (n : ℕ) → Edge n → Bool → Vertex n
  | 0, _, b => b
  | n + 1, (e, _, false), false => Sum.inl (endpoint n e false)
  | _ + 1, (e, i, false), true => Sum.inr (e, i)
  | _ + 1, (e, i, true), false => Sum.inr (e, i)
  | n + 1, (e, _, true), true => Sum.inl (endpoint n e true)

/-- The undirected replacement graph. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) :=
  SimpleGraph.fromRel (fun u v => ∃ e : Edge n, u = endpoint n e false ∧ v = endpoint n e true)

def baseEdge : (n : ℕ) → Edge n
  | 0 => ()
  | n+1 => (baseEdge n,0,false)

lemma endpoint_ne (n : ℕ) (e : Edge n) : endpoint n e false ≠ endpoint n e true := by
  cases n with
  | zero => simp [endpoint]
  | succ n =>
    rcases e with ⟨e,i,b⟩
    cases b <;> simp [endpoint]

lemma adj_iff {n : ℕ} {u v : Vertex n} : (graph n).Adj u v ↔
    ∃ e : Edge n, (u=endpoint n e false ∧ v=endpoint n e true) ∨
      (u=endpoint n e true ∧ v=endpoint n e false) := by
  rw [graph,SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_,⟨e,hu,hv⟩ | ⟨e,hv,hu⟩⟩
    · exact ⟨e,Or.inl ⟨hu,hv⟩⟩
    · exact ⟨e,Or.inr ⟨hu,hv⟩⟩
  · rintro ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact ⟨endpoint_ne n e,Or.inl ⟨e,rfl,rfl⟩⟩
    · exact ⟨(endpoint_ne n e).symm,Or.inr ⟨e,rfl,rfl⟩⟩

lemma adj_endpoint (n : ℕ) (e : Edge n) :
    (graph n).Adj (endpoint n e false) (endpoint n e true) :=
  adj_iff.mpr ⟨e,Or.inl ⟨rfl,rfl⟩⟩

lemma adj_old_mid {n : ℕ} {u : Vertex n} {e : Edge n} {i : ℕ} :
    (graph (n+1)).Adj (Sum.inl u) (Sum.inr (e,i)) ↔
      u=endpoint n e false ∨ u=endpoint n e true := by
  rw [adj_iff]
  constructor
  · rintro ⟨⟨d,j,b⟩,h⟩
    cases b <;> simp [endpoint] at h
    · rcases h with ⟨hu,he,hj⟩
      subst d
      exact Or.inl hu
    · rcases h with ⟨hu,he,hj⟩
      subst d
      exact Or.inr hu
  · rintro (rfl | rfl)
    · exact ⟨(e,i,false),Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨(e,i,true),Or.inr ⟨rfl,rfl⟩⟩

lemma not_adj_old {n : ℕ} (u v : Vertex n) :
    ¬(graph (n+1)).Adj (Sum.inl u) (Sum.inl v) := by
  rintro h
  rcases adj_iff.mp h with ⟨⟨e,i,b⟩,h⟩
  cases b <;> simp [endpoint] at h

lemma not_adj_new {n : ℕ} (u v : Edge n × ℕ) :
    ¬(graph (n+1)).Adj (Sum.inr u) (Sum.inr v) := by
  rintro h
  rcases adj_iff.mp h with ⟨⟨e,i,b⟩,h⟩
  cases b <;> simp [endpoint] at h

lemma replace_adj {n : ℕ} {u v : Vertex n} (h : (graph n).Adj u v) :
    ∃ p : (graph (n+1)).Walk (Sum.inl u) (Sum.inl v), p.length=2 := by
  obtain ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := adj_iff.mp h
  · exact ⟨.cons ((adj_old_mid (i := 0)).mpr (Or.inl rfl))
      (.cons (adj_old_mid.mpr (Or.inr rfl)).symm .nil),rfl⟩
  · exact ⟨.cons ((adj_old_mid (i := 0)).mpr (Or.inr rfl))
      (.cons (adj_old_mid.mpr (Or.inl rfl)).symm .nil),rfl⟩

lemma replace_walk {n : ℕ} {u v : Vertex n} (p : (graph n).Walk u v) :
    ∃ q : (graph (n+1)).Walk (Sum.inl u) (Sum.inl v),q.length=2*p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | cons h p ih =>
    obtain ⟨q,hq⟩ := ih
    obtain ⟨r,hr⟩ := replace_adj h
    refine ⟨r.append q,?_⟩
    rw [SimpleGraph.Walk.length_append,hr,hq,SimpleGraph.Walk.length_cons]
    omega

lemma connected (n : ℕ) : (graph n).Connected := by
  induction n with
  | zero =>
    have : Nonempty (Vertex 0) := ⟨false⟩
    refine ⟨?_⟩
    intro u v
    cases u <;> cases v
    · exact ⟨.nil⟩
    · exact (adj_endpoint 0 ()).reachable
    · exact (adj_endpoint 0 ()).symm.reachable
    · exact ⟨.nil⟩
  | succ n ih =>
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨Sum.inl (endpoint n (baseEdge n) false),?_⟩
    intro v
    cases v with
    | inl v =>
      obtain ⟨p⟩ := ih (endpoint n (baseEdge n) false) v
      obtain ⟨q,hq⟩ := replace_walk p
      exact ⟨q⟩
    | inr v =>
      obtain ⟨e,i⟩ := v
      obtain ⟨p⟩ := ih (endpoint n (baseEdge n) false) (endpoint n e false)
      obtain ⟨q,hq⟩ := replace_walk p
      exact ⟨q.append (adj_old_mid.mpr (Or.inl rfl)).toWalk⟩

lemma potential_walk {V : Type*} {G : SimpleGraph V} (φ : V → ℝ)
    (hφ : ∀ u v,G.Adj u v → |φ u-φ v| ≤ 1) {u v : V} (p : G.Walk u v) :
    |φ u-φ v| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have ht : |φ u-φ w| ≤ |φ u-φ v|+|φ v-φ w| := abs_sub_le _ _ _
    have h := hφ u v h
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

lemma distance_potential (n : ℕ) (a : Vertex n) :
    ∀ u v,(graph n).Adj u v →
      |((graph n).dist a u : ℝ)-(graph n).dist a v| ≤ 1 := by
  intro u v h
  have huv := (connected n).dist_triangle (u := a) (v := u) (w := v)
  have hvu := (connected n).dist_triangle (u := a) (v := v) (w := u)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at huv
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h.symm] at hvu
  have hu : ((graph n).dist a v : ℝ) ≤ (graph n).dist a u+1 := by exact_mod_cast huv
  have hv : ((graph n).dist a u : ℝ) ≤ (graph n).dist a v+1 := by exact_mod_cast hvu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def extendPotential {n : ℕ} (φ : Vertex n → ℝ) : Vertex (n+1) → ℝ
  | Sum.inl u => 2*φ u
  | Sum.inr (e,_) => φ (endpoint n e false)+φ (endpoint n e true)

lemma extendPotential_adj {n : ℕ} (φ : Vertex n → ℝ)
    (hφ : ∀ u v,(graph n).Adj u v → |φ u-φ v| ≤ 1) :
    ∀ u v,(graph (n+1)).Adj u v → |extendPotential φ u-extendPotential φ v| ≤ 1 := by
  intro u v h
  rcases adj_iff.mp h with ⟨⟨e,i,b⟩,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ <;>
    cases b <;> dsimp [endpoint,extendPotential]
  all_goals
    have h := hφ _ _ (adj_endpoint n e)
    have ha := (abs_le.mp h).1
    have hb := (abs_le.mp h).2
    apply abs_le.mpr
    constructor <;> linarith

/-- One subdivision doubles unweighted old-vertex distances. -/
lemma dist_old (n : ℕ) (u v : Vertex n) :
    (graph (n+1)).dist (Sum.inl u) (Sum.inl v)=2*(graph n).dist u v := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := (connected n).exists_walk_length_eq_dist u v
    obtain ⟨q,hq⟩ := replace_walk p
    exact (SimpleGraph.dist_le q).trans (by rw [hq,hp])
  · obtain ⟨p,hp⟩ := (connected (n+1)).exists_walk_length_eq_dist (Sum.inl u) (Sum.inl v)
    have h := potential_walk (extendPotential (fun w => ((graph n).dist u w : ℝ)))
      (extendPotential_adj _ (distance_potential n u)) p
    rw [hp] at h
    simp only [extendPotential,SimpleGraph.dist_self,Nat.cast_zero,mul_zero,zero_sub,abs_neg] at h
    rw [abs_of_nonneg (by positivity)] at h
    exact_mod_cast h

lemma dist_siblings (n : ℕ) (e : Edge n) {i j : ℕ} (hij : i ≠ j) :
    (graph (n+1)).dist (Sum.inr (e,i)) (Sum.inr (e,j))=2 := by
  apply le_antisymm
  · exact SimpleGraph.dist_le (.cons (adj_old_mid.mpr (Or.inl rfl)).symm
      (.cons (adj_old_mid.mpr (Or.inl rfl)) .nil))
  · apply Nat.succ_le_of_lt
    apply (connected (n+1)).one_lt_dist_of_ne_of_not_adj
    · intro h
      exact hij (Prod.mk.inj (Sum.inr.inj h)).2
    · exact not_adj_new _ _

theorem two_atLeastTwo : Nat.AtLeastTwo (1 + 1) := inferInstance

/-- Final edges have length 2⁻ᵏ: this is the shortest-path metric of the normalized graph. -/
def distance (k : ℕ) (u v : Vertex k) : ℝ :=
  ((graph k).dist u v : ℝ) / (Nat.cast 2 : ℝ) ^ k

/-- The standing all-pairs distortion hypothesis, with its positive arbitrary scale. -/
def HasDistortion {X : Type*} [NormedAddCommGroup X]
    (k : ℕ) (f : Vertex k → X) (D s : ℝ) : Prop :=
  1 ≤ D ∧ 0 < s ∧ ∀ u v,
    s * distance k u v ≤ ‖f u - f v‖ ∧
    ‖f u - f v‖ ≤ D * s * distance k u v

lemma distance_old (n : ℕ) (u v : Vertex n) :
    distance (n+1) (Sum.inl u) (Sum.inl v)=distance n u v := by
  rw [distance,distance,dist_old,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  field_simp

lemma distance_edge (n : ℕ) (e : Edge n) :
    distance n (endpoint n e false) (endpoint n e true)=1/(2:ℝ)^n := by
  rw [distance,SimpleGraph.dist_eq_one_iff_adj.mpr (adj_endpoint n e),Nat.cast_one,Nat.cast_ofNat]

lemma distance_siblings (n : ℕ) (e : Edge n) {i j : ℕ} (hij : i ≠ j) :
    distance (n+1) (Sum.inr (e,i)) (Sum.inr (e,j))=2/(2:ℝ)^(n+1) := by
  rw [distance,dist_siblings n e hij,Nat.cast_ofNat]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The oriented slope of a stage edge in the normalized metric. -/
def slope {n : ℕ} (f : Vertex n → X) (e : Edge n) : X :=
  (2:ℝ)^n • (f (endpoint n e true)-f (endpoint n e false))

/-- Midpoint deviations normalized by the lengths of the parent edges. -/
def deviation {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i : ℕ) : X :=
  (2:ℝ)^n • ((2:ℝ) • f (Sum.inr (e,i))-
    f (Sum.inl (endpoint n e false))-f (Sum.inl (endpoint n e true)))

lemma slope_plus_deviation {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i : ℕ) :
    slope (fun v => f (Sum.inl v)) e+deviation f e i=slope f (e,i,false) := by
  dsimp [slope,deviation,endpoint]
  rw [pow_succ]
  module

lemma slope_minus_deviation {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i : ℕ) :
    slope (fun v => f (Sum.inl v)) e-deviation f e i=slope f (e,i,true) := by
  dsimp [slope,deviation,endpoint]
  rw [pow_succ]
  module

lemma deviation_sub {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i j : ℕ) :
    deviation f e i-deviation f e j=
      (2:ℝ)^(n+1) • (f (Sum.inr (e,i))-f (Sum.inr (e,j))) := by
  dsimp [deviation]
  rw [pow_succ]
  module

lemma deviation_separated {n : ℕ} (f : Vertex (n+1) → X) {s : ℝ}
    (hl : ∀ u v,s*distance (n+1) u v ≤ ‖f u-f v‖) (e : Edge n)
    {i j : ℕ} (hij : i ≠ j) : 2*s ≤ ‖deviation f e i-deviation f e j‖ := by
  rw [deviation_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2:ℝ)^(n+1))]
  calc
    2*s = (2:ℝ)^(n+1)*(s*distance (n+1) (Sum.inr (e,i)) (Sum.inr (e,j))) := by
      rw [distance_siblings n e hij]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hl _ _) (by positivity)

/-- An infinite separated symmetric lens with the exact quadratic constant. -/
def QuadraticLens (X : Type*) [NormedAddCommGroup X] : Prop :=
  ∀ (x : X) (z : ℕ → X) (R ε : ℝ),0 ≤ R → 0 < ε →
    (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
    (∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) → ‖x‖^2+ε^2/16 ≤ R^2

/-- Supremum-free squared stretch-loss induction. The bound on all final-edge
    slopes loses s²/4 at each backward step. No maximum child is used. -/
lemma squared_stretch_loss (hX : QuadraticLens X) (k : ℕ) (f : Vertex k → X)
    {s B : ℝ} (hs : 0 < s)
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖)
    (hb : ∀ e,‖slope f e‖^2 ≤ B) : s^2*(1+(k:ℝ)/4) ≤ B := by
  induction k generalizing B with
  | zero =>
    have h := hl (endpoint 0 () false) (endpoint 0 () true)
    rw [distance_edge] at h
    have h0 := hb ()
    simp only [slope,pow_zero,one_smul,norm_sub_rev] at h0
    norm_num at h ⊢
    nlinarith [sq_nonneg (s-‖f (endpoint 0 () false)-f (endpoint 0 () true)‖)]
  | succ n ih =>
    have hB : 0 ≤ B := (sq_nonneg _).trans (hb (baseEdge (n+1)))
    have hold : ∀ e,‖slope (fun v => f (Sum.inl v)) e‖^2 ≤ B-s^2/4 := by
      intro e
      have hp : ∀ i,‖slope (fun v => f (Sum.inl v)) e+deviation f e i‖ ≤ Real.sqrt B := by
        intro i
        rw [slope_plus_deviation]
        exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hb _)
      have hm : ∀ i,‖slope (fun v => f (Sum.inl v)) e-deviation f e i‖ ≤ Real.sqrt B := by
        intro i
        rw [slope_minus_deviation]
        exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hb _)
      have h := hX (slope (fun v => f (Sum.inl v)) e) (deviation f e)
        (Real.sqrt B) (2*s) (Real.sqrt_nonneg _) (by positivity) hp hm
        (fun _ _ hij => deviation_separated f hl e hij)
      rw [Real.sq_sqrt hB] at h
      nlinarith
    have hlo : ∀ u v,s*distance n u v ≤ ‖f (Sum.inl u)-f (Sum.inl v)‖ := by
      intro u v
      simpa only [distance_old] using hl (Sum.inl u) (Sum.inl v)
    have hind := ih (fun v => f (Sum.inl v)) hlo hold
    push_cast
    linarith

lemma distortion_bound (hX : QuadraticLens X) (k : ℕ) (f : Vertex k → X)
    (D s : ℝ) (h : HasDistortion k f D s) : 1+(k:ℝ)/4 ≤ D^2 := by
  obtain ⟨hD,hs,h⟩ := h
  have hbound : ∀ e,‖slope f e‖^2 ≤ (D*s)^2 := by
    intro e
    have he := (h (endpoint k e false) (endpoint k e true)).2
    rw [distance_edge] at he
    have hh : ‖slope f e‖ ≤ D*s := by
      rw [slope,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2:ℝ)^k),norm_sub_rev]
      calc
        _ ≤ (2:ℝ)^k*(D*s*(1/(2:ℝ)^k)) := mul_le_mul_of_nonneg_left he (by positivity)
        _ = _ := by field_simp
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) hs.le)).mpr hh
  have hb := squared_stretch_loss hX k f hs (fun u v => (h u v).1) hbound
  have hp : 0 < s^2 := sq_pos_of_pos hs
  have hmul : s^2*(1+(k:ℝ)/4) ≤ s^2*D^2 := by nlinarith only [hb]
  exact (mul_le_mul_iff_right₀ hp).mp hmul

end Diamond

/-- The exact two-model unconditional headline; neither intrinsic estimate is a hypothesis. -/
def Headline : Prop :=
  (∀ (k : ℕ) (f : Diamond.Vertex k → ForestDual) (D s : ℝ),
    Diamond.HasDistortion k f D s → 1 + (k : ℝ) / 4 ≤ D ^ 2) ∧
  (∀ (k : ℕ) (f : Diamond.Vertex k → InfinitePredual) (D s : ℝ),
    Diamond.HasDistortion k f D s → 1 + (k : ℝ) / 4 ≤ D ^ 2)

/-- The finite forest lens property follows from the proved pooled estimate and
    the proved approximation of its full dual. -/
theorem forest_quadratic_lens : Diamond.QuadraticLens ForestDual := by
  intro x z R ε hR hε hp hm hs
  exact Ancestry.separated_lens (A := forestAncestry) forest_finite_heads
    (fun η hη => Forest.full_dual_approximation x hη) z hR hε hp hm hs

/-- The infinite-height assertion is only for its closed coordinate span,
    not for the full infinite-height dual. -/
theorem infinite_quadratic_lens : Diamond.QuadraticLens InfinitePredual := by
  intro x z R ε hR hε hp hm hs
  exact Ancestry.separated_lens (A := infiniteAncestry) infinite_finite_heads
    (fun η hη => Ancestry.coordinate_predual_approximation (A := infiniteAncestry)
      infinite_finite_heads x.property hη) (fun i => (z i).val) hR hε hp hm hs

theorem headline : Headline := by
  constructor
  · exact fun k f D s h => Diamond.distortion_bound forest_quadratic_lens k f D s h
  · exact fun k f D s h => Diamond.distortion_bound infinite_quadratic_lens k f D s h

end DiamondDistortion

end

end OAI
