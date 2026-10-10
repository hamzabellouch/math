import OAI.Combinatorics.ContingencyTables.Transport.RecursiveSignedTransport

namespace OAI

/-!
# Finite softened-weight transport limits

The explicit root coefficient has only the two endpoint masses in its
weight-dependent denominators. All puncture masses and edge energies are
finite sums of continuous functions of weights. Thus the actual proved
one-hole transport survives zero internal weights when the two limiting
endpoint masses are positive.
-/

namespace ContingencyTables.HardZeroTransport

open scoped BigOperators Classical Matrix Topology
open CommonBasesFPRAS BinaryContraction RecursiveSignedTransport
open Filter

variable {Γ K : Type*} [Fintype Γ] [DecidableEq Γ] {l : Filter K}

omit [DecidableEq Γ] in
lemma coeffDerivs_tendsto (as : List (Γ → ℝ)) (F : K → Set Γ → ℝ) (f : Set Γ → ℝ)
    (hlim : ∀ S, Tendsto (fun t => F t S) l (nhds (f S))) (A : Set Γ) :
    Tendsto (fun t => coeffDerivs as (F t) A) l (nhds (coeffDerivs as f A)) := by
  induction as generalizing A with
  | nil => exact hlim A
  | cons a as ih =>
    change Tendsto (fun t => ∑ i, if i ∈ A then 0 else a i*coeffDerivs as (F t) (insert i A)) l _
    apply tendsto_finsetSum
    intro i _
    by_cases hi : i ∈ A
    · simpa only [hi,ite_true] using (tendsto_const_nhds : Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))
    · simpa only [hi,ite_false] using (tendsto_const_nhds.mul (ih (insert i A)))

lemma slotTotal_tendsto (ps : List (Γ × Γ)) (F : K → Set Γ → ℝ) (f : Set Γ → ℝ)
    (hlim : ∀ S, Tendsto (fun t => F t S) l (nhds (f S))) (A : Set Γ) :
    Tendsto (fun t => slotTotal ps (F t) A) l (nhds (slotTotal ps f A)) :=
  coeffDerivs_tendsto (ps.map pairDirection) F f hlim A

lemma slotTotal_weighted_tendsto (ps : List (Γ × Γ)) (F : K → Set Γ → ℝ) (f H : Set Γ → ℝ)
    (hlim : ∀ S, Tendsto (fun t => F t S) l (nhds (f S))) (A : Set Γ) :
    Tendsto (fun t => slotTotal ps (fun S => F t S*H S) A) l
      (nhds (slotTotal ps (fun S => f S*H S) A)) :=
  slotTotal_tendsto ps _ _ (fun S => (hlim S).mul_const (H S)) A

private lemma list_sum_tendsto {A : Type*} (xs : List A) (u : K → A → ℝ) (v : A → ℝ)
    (hu : ∀ a, Tendsto (fun t => u t a) l (nhds (v a))) :
    Tendsto (fun t => (xs.map (u t)).sum) l (nhds ((xs.map v).sum)) := by
  induction xs with
  | nil => simpa using (tendsto_const_nhds : Tendsto (fun _ : K => (0:ℝ)) l (nhds 0))
  | cons a xs ih => simpa only [List.map_cons,List.sum_cons] using (hu a).add ih

lemma rootCoefficient_tendsto (ps : List (Γ × Γ)) (F : K → Set Γ → ℝ) (f : Set Γ → ℝ)
    (hlim : ∀ S, Tendsto (fun t => F t S) l (nhds (f S)))
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ)
    (hsp : slotTotal ps f (insert p A) ≠ 0) (hsd : slotTotal ps f (insert d A) ≠ 0)
    (hW : ∀ i, W i ≠ 0) :
    Tendsto (fun t => rootCoefficient ps (F t) A p d W) l (nhds (rootCoefficient ps f A p d W)) := by
  have hp := slotTotal_tendsto ps F f hlim (insert p A)
  have hd := slotTotal_tendsto ps F f hlim (insert d A)
  have hs := list_sum_tendsto (slotPunctures ps)
    (fun t x => slotTotal x.2 (F t) (insert p (insert d A))/W x.1.1)
    (fun x => slotTotal x.2 f (insert p (insert d A))/W x.1.1)
    (fun x => (slotTotal_tendsto x.2 F f hlim _).div_const _)
  unfold rootCoefficient
  exact ((tendsto_const_nhds.div (hp.mul_const (W p)) (mul_ne_zero hsp (hW p))).add
    (tendsto_const_nhds.div (hd.mul_const (W d)) (mul_ne_zero hsd (hW d)))).add
      ((tendsto_const_nhds.div (hp.mul hd) (mul_ne_zero hsp hsd)).mul hs)

omit [Fintype Γ] [DecidableEq Γ] in
lemma slotGraphEnergy_tendsto {I : Type*} [Fintype I]
    (ps : List (Γ × Γ)) (F : K → Set Γ → ℝ) (f H : Set Γ → ℝ)
    (hlim : ∀ S, Tendsto (fun t => F t S) l (nhds (f S)))
    (A : Set Γ) (e : I → Γ) (W : Γ → ℝ) :
    Tendsto (fun t => slotGraphEnergy ps (F t) H A e W) l (nhds (slotGraphEnergy ps f H A e W)) := by
  unfold slotGraphEnergy
  apply Tendsto.div_const
  apply tendsto_finsetSum
  intro ST _
  unfold slotEdgeEnergy
  exact (((hlim ST.1).const_mul _).min ((hlim ST.2).const_mul _)).mul_const _

/-- The original finite transport inequality at nonnegative limiting
weights. Only the two actual endpoint masses need to stay positive. -/
theorem transport_graph_bound_degree_limit
    [l.NeBot]
    (ps : List (Γ × Γ)) (F : K → Set Γ → ℝ) (f H : Set Γ → ℝ)
    (hlim : ∀ S, Tendsto (fun t => F t S) l (nhds (f S)))
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) (k : ℕ)
    (hsoft : ∀ᶠ t in l, DegreePositive (F t) k ∧ AdditionProperty (F t) k)
    (hdegree : A.ncard+ps.length+1=k) (hpd : p≠d) (hpA : p∉A) (hdA : d∉A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p∈ps, W p.1=W p.2)
    (hsp : 0 < slotTotal ps f (insert p A)) (hsd : 0 < slotTotal ps f (insert d A)) :
    (slotTotal ps (fun S => f S*H S) (insert p A)/slotTotal ps f (insert p A) -
      slotTotal ps (fun S => f S*H S) (insert d A)/slotTotal ps f (insert d A))^2 ≤
      rootCoefficient ps f A p d W * slotGraphEnergy ps f H A (rootEmbedding p d) W := by
  have hp := slotTotal_tendsto ps F f hlim (insert p A)
  have hd := slotTotal_tendsto ps F f hlim (insert d A)
  have hpn := slotTotal_weighted_tendsto ps F f H hlim (insert p A)
  have hdn := slotTotal_weighted_tendsto ps F f H hlim (insert d A)
  have hc := rootCoefficient_tendsto ps F f hlim A p d W (ne_of_gt hsp) (ne_of_gt hsd)
    (fun i => ne_of_gt (hW i))
  have he := slotGraphEnergy_tendsto ps F f H hlim A (rootEmbedding p d) W
  apply le_of_tendsto_of_tendsto (((hpn.div hp (ne_of_gt hsp)).sub (hdn.div hd (ne_of_gt hsd))).pow 2) (hc.mul he)
  filter_upwards [hsoft] with t ht
  exact transport_graph_bound_degree ps (F t) H A p d W k ht.1 ht.2 hdegree
    hpd hpA hdA hps hW hw

/-- Hard-zero transport in the manuscript's original omission convention,
obtained from the actual positive softened lifts and finite limits. -/
theorem one_hole_transport_limit
    [l.NeBot]
    (ps : List (Γ × Γ)) (F : K → Set Γ → ℝ) (f H : Set Γ → ℝ)
    (hlim : ∀ S, Tendsto (fun t => F t S) l (nhds (f S)))
    (A : Set Γ) (p d : Γ) (W : Γ → ℝ) (k : ℕ) (hk : k ≤ Fintype.card Γ)
    (hsoft : ∀ᶠ t in l, DegreePositive (F t) k ∧ OmissionProperty (F t) k)
    (hdegree : A.ncard+ps.length+1=Fintype.card Γ-k)
    (hpd : p≠d) (hpA : p∉A) (hdA : d∉A)
    (hps : SlotsFresh ps (A ∪ Set.range (rootEmbedding p d)))
    (hW : ∀ i, 0 < W i) (hw : ∀ p∈ps, W p.1=W p.2)
    (hsp : 0 < slotTotal ps (complementWeight f) (insert p A))
    (hsd : 0 < slotTotal ps (complementWeight f) (insert d A)) :
    let fc := complementWeight f
    let Hc := complementWeight H
    (slotTotal ps (fun S => fc S*Hc S) (insert p A)/slotTotal ps fc (insert p A) -
      slotTotal ps (fun S => fc S*Hc S) (insert d A)/slotTotal ps fc (insert d A))^2 ≤
      rootCoefficient ps fc A p d W * slotGraphEnergy ps fc Hc A (rootEmbedding p d) W := by
  apply transport_graph_bound_degree_limit ps (fun t => complementWeight (F t))
    (complementWeight f) (complementWeight H) (fun S => hlim Sᶜ) A p d W (Fintype.card Γ-k)
  · filter_upwards [hsoft] with t ht
    exact ⟨complement_degreePositive (F t) k hk ht.1,ht.2⟩
  · exact hdegree
  · exact hpd
  · exact hpA
  · exact hdA
  · exact hps
  · exact hW
  · exact hw
  · exact hsp
  · exact hsd

end ContingencyTables.HardZeroTransport

end OAI
