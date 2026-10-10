import OAI.Combinatorics.HadwigerCounterexample.SuperlevelBounds

namespace OAI

/-! # Rare Leaf Events -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N K s0:ℕ}
namespace StatusAnalysis
variable {q:Format} {d e:Rates} {b:Bool}

namespace Quill
variable (w:Quill p q d b) (m:Mixer p n) (t : Tagging p (Messenger q))
    (z : Messenger q→F)
def qualified (s:Charts p n d) (K :ℕ) (μ:Wgt (UnitType p n N)) (P : UnitType p n N→Prop) (a:ℝ) :=
    2*a ≤ pr μ P ∧ ∀ i,P i →μ i ≠0→ w.steady t z m K s i

theorem qualify_hit (s : Charts p n d) (K:ℕ) (μ:Wgt (UnitType p n N))
    (P: UnitType p n N→Prop) (H:Keys (p:=p) t N→Prop) {a α:ℝ} (hα:0<α)
    (h:w.qualified m t z s K μ P a)
    (hw : IsLaw μ) (hg:∀ i,IsLaw (w.policies t z n i))
    (hp: pr μ (fun i=>¬w.sober t z K H m α i) ≤ a) :
    a*α ≤ pr (w.sales t z μ P m s) H := by
  classical
  let Q:=w.sober t z K H m α
  let V i:=w.prowl s t z m i (fun i=>ind (H i))
  have he:a ≤ pr μ (fun x=>P x∧ Q x) :=
    (le_trans (by linarith only [hp,h.1]) (pr_shield hw.nz _ _))
  unfold pr; rw [sales_mean]
  refine (mul_le_mul_of_nonneg_right he hα.le).trans ?_
  unfold pr; rw [←avg_mul]
  unfold avg
  refine Finset.sum_le_sum fun i _=> ?_
  dsimp only
  by_cases hi:μ i=0
  · simp only [hi,zero_mul]; rfl
  refine mul_le_mul_of_nonneg_left ?_ (hw.nz i)
  have hv : 0≤ V i := avg_nonneg (prodW_law hg).nz (fun j=> mul_nonneg (ind_nonneg _) (ind_nonneg _))
  by_cases hP:P i∧ Q i
  · change ind (_∧_) *_ ≤ _*V i; rw [ind_one hP,ind_one hP.1,one_mul,one_mul]
    exact hP.2 s (h.2 i hP.1 hi)
  rw [ind_zero hP,zero_mul]; exact mul_nonneg (ind_nonneg _) hv
end Quill

namespace Station
variable {w:LeafMixture p n N} (t:Station p n N K w) (x:Typus p q d e)
    (m:Mixer p n) (k: Fin (2^deckMax p K)) (μ:Wgt (UnitType p n N))

def charter (a:ℝ) (i:w.T×w.T) :=
    x.permission ∧
      x.qA.qualified m x.t x.z (t.cAxes i.1 d) K (partW μ i.1.val) (t.frontPage x m i.1 i.2 k) a ∧
      x.qB.qualified m x.t x.z (t.cAxes i.2 e) K (partW μ i.2.val) (t.backPage x m i.1 i.2 k) a

def berth (a:ℝ) :=
    pr (pairW (portionW μ w.T) (portionW μ w.T)) (charter t x m k μ a)

theorem charterWeak {a b:ℝ} (hh:a≤b) (i:w.T×w.T) (hf:charter t x m k μ b i) :
    charter t x m k μ a i :=
  ⟨hf.1,⟨(mul_le_mul_of_nonneg_left hh (by norm_num)).trans hf.2.1.1,hf.2.1.2⟩,
    ⟨(mul_le_mul_of_nonneg_left hh (by norm_num)).trans hf.2.2.1,hf.2.2.2⟩⟩
end Station

variable {A I J : Type} [Fintype A] [Fintype I] [Fintype J]
set_option maxHeartbeats 800000 in
theorem vacantBound (w : Wgt I) (v : I→ Wgt A) (K : I→ J → A→Prop) (P : A→Prop)
    (hw:IsLaw w) (hv:∀ i,IsLaw (v i))
    {b e ε:ℝ} (hb : 0<b)
    (he : ∀ i j,pr (mixW w v) (K i j) ≤ e)
    (hf : pr (mixW w v) P≤ε) :
    let S (i:I×I) := (∃ j,b< pr (v i.1) (K i.2 j)) ∨ b< pr (v i.2) P
    pr (pairW w w) S ≤ num J * (e/b)+ε/b := by
  classical
  intro S
  have hg Q c (h: pr (mixW w v) Q≤c) : pr w (fun i=> b< pr (v i) Q)≤ c/b := by
    refine (le_div_iff₀ hb).mpr ?_
    rw [mul_comm]
    unfold pr at h; rw [mixW_avg] at h
    let f i:=pr (v i) Q
    apply le_trans (b:=avg w f) ?_ h
    exact le_trans (mul_le_mul_of_nonneg_left (pr_mono hw.nz
      (q:=fun i=>b≤f i) (fun _ hh=>hh.le)) hb.le) (le_avg_markov hw.nz (fun i=> pr_nonneg (hv _).nz) b)
  let Q i:= pr w (fun x=>∃ j,b<pr (v x) (K i j))
  have hh i : Q i≤num J*(e/b) := ((pr_exists_le hw.nz _).trans
    (Finset.sum_le_sum fun j _ => hg _ _ (he i j))).trans_eq (by simp [num])
  let U (i:I×I):=∃ j,b<pr (v i.1) (K i.2 j)
  let V (i:I×I):=b<pr (v i.2) P
  apply (pr_or_le (p:=U) (q:=V) (pairW_law hw hw).nz).trans
  refine add_le_add ?_ ?_
  · unfold pr; rw [pairW_avg,avg_avg]; exact hw.avg_le hh
  unfold pr; rw [pairW_avg ]; exact hw.avg_le fun _=>hg _ _ hf

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
