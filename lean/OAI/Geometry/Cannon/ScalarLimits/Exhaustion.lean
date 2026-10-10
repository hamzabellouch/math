import Mathlib
import OAI.Geometry.Cannon.Energy.MeshEnergySumFilter

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators
open Set Topology

namespace CannonDiagonal

open Set Metric Filter Topology CannonApprox

lemma select_strictMono_of_eventually (P : ℕ → ℕ → Prop)
    (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, P j (φ j) := by
  classical
  choose m hm using fun j => eventually_atTop.mp (hP j)
  let φ : ℕ → ℕ := fun j => Nat.rec (m 0) (fun k x => max (x+1) (m (k+1))) j
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ (fun j =>
    (Nat.lt_succ_self (φ j)).trans_le (Nat.le_max_left _ _))
  refine ⟨φ,hφ,fun j => hm j (φ j) ?_⟩
  cases j with
  | zero => exact le_rfl
  | succ j => exact Nat.le_max_right _ _

def exhaustion {X : Type*} [MetricSpace X] (b : X) (j : ℕ) : Set X :=
  {x | 1/((j:ℝ)+1) ≤ dist x b}

lemma exhaustion_isCompact {X : Type*} [MetricSpace X] [CompactSpace X]
    (b : X) (j : ℕ) : IsCompact (exhaustion b j) :=
  (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact

lemma not_mem_exhaustion {X : Type*} [MetricSpace X] (b : X) (j : ℕ) :
    b ∉ exhaustion b j := by
  simp only [exhaustion,mem_ofPred_eq,dist_self,not_le]
  positivity

lemma compact_eventually_subset_exhaustion {X : Type*} [MetricSpace X]
    (b : X) {K : Set X} (hK : IsCompact K) (hb : b ∉ K) :
    ∀ᶠ j in atTop, K ⊆ exhaustion b j := by
  by_cases hKn : K.Nonempty
  · obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hKn (continuous_id.dist continuous_const).continuousOn
    have hpos : 0 < dist x b := dist_pos.mpr (fun h => hb (h ▸ hx))
    have ht : ∀ᶠ j : ℕ in atTop, 1/((j:ℝ)+1) < dist x b :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hpos
    filter_upwards [ht] with j hj
    intro y hy
    exact hj.le.trans (hmin hy)
  · simp only [not_nonempty_iff_eq_empty] at hKn
    simp [hKn]

lemma enlarged_cells_eventually_subset {X : Type*} [MetricSpace X]
    (ι : ℕ → Type*) (p : ∀ n, ι n → X) (r : ℕ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (J : ℝ)
    {K S : Set X} (hK : IsCompact K) (hS : IsOpen S) (hKS : K ⊆ S) :
    ∀ᶠ n in atTop, ∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
      closedBall (p n i) (J*r n) ⊆ S := by
  obtain ⟨δ,hδ,hδS⟩ := hK.exists_thickening_subset_open hS hKS
  have ht : Tendsto (fun n => (J+2)*r n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hr :
      Tendsto (fun n => (J+2)*r n) atTop (𝓝 ((J+2)*0)))
  filter_upwards [ht.eventually_lt_const hδ] with n hn
  intro i hi z hz
  obtain ⟨x,hxi,hxK⟩ := hi
  apply hδS
  refine mem_thickening_iff.mpr ⟨x,hxK,?_⟩
  have hzx := dist_triangle z (p n i) x
  have hxball : dist (p n i) x < 2*r n := by
    simpa only [mem_ball,dist_comm] using hxi
  have hzball : dist z (p n i) ≤ J*r n := mem_closedBall.mp hz
  linarith

theorem common_mesh_diagonal {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (b : X) (S : ℕ → Set X) (hS : ∀ i, IsOpen (S i))
    (F : ℕ → X → ℝ) (W : X → ℝ) (G : ℕ → ℕ → X → ℝ)
    (hF : ∀ K : Set X, IsCompact K → b ∉ K →
      TendstoUniformlyOn F W atTop K)
    (hdom : ∀ K : Set X, IsCompact K → b ∉ K → ∀ᶠ i in atTop, K ⊆ S i)
    (hG : ∀ i K, IsCompact K → K ⊆ S i →
      TendstoUniformlyOn (G i) (F i) atTop K)
    (hGbounded : ∀ i n, BddAbove (range (G i n)) ∧ BddBelow (range (G i n)))
    (hE : ∀ i K, IsCompact K → K ⊆ S i → ∀ J : ℝ, 0 < J →
      Tendsto (fun n => meshEnergy (p n) (r n) J (G i n) K) atTop (𝓝 0)) :
    ∃ α N : ℕ → ℕ, StrictMono α ∧ StrictMono N ∧
      (∀ K : Set X, IsCompact K → b ∉ K →
        TendstoUniformlyOn (fun j => G (α j) (N j)) W atTop K) ∧
      (∀ K : Set X, IsCompact K → b ∉ K → ∀ J : ℝ, 0 < J →
        Tendsto (fun j => meshEnergy (p (N j)) (r (N j)) J (G (α j) (N j)) K)
          atTop (𝓝 0) ∧
        ∀ᶠ j in atTop, ∀ i, (ball (p (N j) i) (2*r (N j)) ∩ K).Nonempty →
          closedBall (p (N j) i) (J*r (N j)) ⊆ S (α j)) := by
  classical
  let ε : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hε : ∀ j, 0 < ε j := fun j => by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let K : ℕ → Set X := exhaustion b
  have hK : ∀ j, IsCompact (K j) := exhaustion_isCompact b
  have hbK : ∀ j, b ∉ K j := not_mem_exhaustion b
  obtain ⟨α,hα,hαspec⟩ := select_strictMono_of_eventually
    (fun j i => K j ⊆ S i ∧ ∀ x ∈ K j, dist (W x) (F i x) < ε j) (by
      intro j
      exact (hdom _ (hK j) (hbK j)).and
        (Metric.tendstoUniformlyOn_iff.mp (hF _ (hK j) (hbK j)) _ (hε j)))
  obtain ⟨N,hN,hNspec⟩ := select_strictMono_of_eventually
    (fun j n => (∀ x ∈ K j, dist (F (α j) x) (G (α j) n x) < ε j) ∧
      meshEnergy (p n) (r n) ((j:ℝ)+1) (G (α j) n) (K j) < ε j ∧
      ∀ i, (ball (p n i) (2*r n) ∩ K j).Nonempty →
        closedBall (p n i) (((j:ℝ)+1)*r n) ⊆ S (α j)) (by
      intro j
      exact (Metric.tendstoUniformlyOn_iff.mp
          (hG (α j) _ (hK j) (hαspec j).1) _ (hε j)).and
        (((hE (α j) _ (hK j) (hαspec j).1 ((j:ℝ)+1) (by positivity)).eventually_lt_const
          (hε j)).and (enlarged_cells_eventually_subset ι p r hrlim _ (hK j)
          (hS (α j)) (hαspec j).1)))
  refine ⟨α,N,hα,hN,?_,?_⟩
  · intro T hT hbT
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    have ht : ∀ᶠ j in atTop, 2*ε j < η := by
      have hh : Tendsto (fun j => 2*ε j) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_const_nhds.mul hεlim :
          Tendsto (fun j => 2*ε j) atTop (𝓝 (2*0)))
      exact hh.eventually_lt_const hη
    filter_upwards [compact_eventually_subset_exhaustion b hT hbT,ht] with j hj hjη
    intro x hx
    exact (dist_triangle (W x) (F (α j) x) (G (α j) (N j) x)).trans_lt
      ((add_lt_add ((hαspec j).2 x (hj hx)) ((hNspec j).1 x (hj hx))).trans_le
        (by linarith))
  · intro T hT hbT J hJ
    have htJ : ∀ᶠ j : ℕ in atTop, J ≤ (j:ℝ)+1 := by
      obtain ⟨m,hm⟩ := exists_nat_ge J
      filter_upwards [eventually_ge_atTop m] with j hj
      have hh : (m:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
      linarith
    have hsmall : ∀ᶠ j in atTop,
        meshEnergy (p (N j)) (r (N j)) J (G (α j) (N j)) T ≤ ε j := by
      filter_upwards [compact_eventually_subset_exhaustion b hT hbT,htJ] with j hj hjJ
      exact (meshEnergy_mono_set _ _ _ _ hj).trans
        ((meshEnergy_mono_radius _ _ (hr (N j)).le _ (hGbounded _ _).1
          (hGbounded _ _).2 _ hJ.le hjJ).trans (hNspec j).2.1.le)
    refine ⟨squeeze_zero' (Eventually.of_forall (fun j => meshEnergy_nonneg _ _ _ _ _))
      hsmall hεlim,?_⟩
    filter_upwards [compact_eventually_subset_exhaustion b hT hbT,htJ] with j hj hjJ
    intro i hi
    exact (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hjJ (hr (N j)).le)).trans
      ((hNspec j).2.2 i (hi.mono (inter_subset_inter_right _ hj)))

end CannonDiagonal

end
end
end
end
end
end
end
end
end
end

end OAI
