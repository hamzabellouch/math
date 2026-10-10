import OAI.Combinatorics.HadwigerCounterexample.CellPositivityScales

namespace OAI

/-! # Conditional Signature Positivity -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K r d : ℕ}
namespace StatusAnalysis
open Template

namespace Appearance
variable (x : Appearance p) (Y : Silhouette p N r)

theorem smudges (o : UnitType p n N) (m:Mixer p n) (v : Ax p n d) (i:Nodes) (j : Knobs p.g n) :
    (x.profile i o m v j).2.1=((scan p x.l x.f j).diagO,stains x.trot m v j) := by
  apply Prod.ext
  · exact role_scan p _ _ _ _
  funext i; exact T_swap m _ _

def nearly (p: Shape) (z: Digest p.g) (u: Par d) (x: Magazine p d) :=
  x.1=z∧ x.2.1=u

set_option maxHeartbeats 800000 in
theorem demonstrates (o : UnitType p n N) {m : Mixer p n}
    (v : Ax p n d) (K:ℕ) (i:Nodes) (j:Fin r) (δ : ℝ) (hd:0<δ)
    (z : Digest p.g) (u:Cell d)
    (he : z.feasible x.l x.f) (hf : z.sumBit=x.q) (ht : 1≤p.r) (hn : 2*p.r≤n)
    (hh : δ≤ x.reference Y j)
    (hs : smoothSilk p δ δ Y m K (onSide o i)) (hK : d≤K^2)
    (hV : Injective v) (hv : ∀ x,totalRank (v x) ≤ K) :
    basebeta p K/2 ≤ pr (x.reflected Y i o m v j) (nearly p z (z.diagO,u)) := by
  classical
  have ha : x.apt := ⟨z,he,hf⟩
  let μ:= x.reference Y j
  let f := onSide o i
  obtain ⟨hM,hB⟩:= hs x
  specialize hM ha
  specialize hB z j he hf hh
  let U (y:AtomKey (p:=p) (x.trot.t ()) N) := Y x.l x.q y=j
  have hm : basebeta p K*μ ≤
      pr (x.wit n) (fun y=> (scan p x.l x.f y=z∧Y x.l x.q (x.face f y)=j) ∧
        stains x.trot m v y=u) := by
    let h := patrol_beta x.trot U m K z he ht hn f
    dsimp only at h
    rw [hf] at h
    exact h hB d hK v hV hv u
  let w := nearly p z (z.diagO,u)
  have hq (y : Knobs p.g n) :
      (scan p x.l x.f y=z ∧ Y x.l x.q (x.face f y)=j) ∧ stains x.trot m v y=u →
        x.showTag Y (onSide o i) y=j∧ w (x.profile i o m v y) := by
    rintro ⟨⟨h,h1⟩,h2⟩
    refine ⟨h1,h,?_⟩; rw [smudges,h,h2]
  have hW := witLaw ha ht hn
  have heq := (hm.trans (pr_mono hW.nz hq)).trans_eq (x.show_pr Y i o m v hW j w)
  let ν:= x.empirical Y f j
  have h2 : ν ≤ 2*μ := by
    have hz : |μ-ν|≤δ := le_trans
      (Finset.single_le_sum (fun k _ => abs_nonneg (x.reference Y k-x.empirical Y f k))
        (Finset.mem_univ j)) hM
    change δ≤ μ at hh
    linarith [(abs_le.mp hz).1]
  let Q := pr (x.reflected Y i o m v j) w
  have h3 : basebeta p K*μ≤ ν*Q := heq
  have ht := mul_le_mul_of_nonneg_right h2
    (show 0≤ Q from pr_nonneg (x.reflectedLaw Y hW i o m v j).nz)
  apply le_of_mul_le_mul_right _ (hd.trans_le hh)
  change _*μ ≤ Q*μ
  linarith only [h3,ht]

def fitsink (x : Appearance p) (w : Magazine p d) :=
   w.1.feasible x.l x.f ∧ w.1.sumBit=x.q ∧ w.1.diagO=w.2.1.1
theorem rawink (x : Appearance p) (m : Mixer p n) (i : Nodes) (o : UnitType p n N)
    (v : Ax p n d) :
    carried (x.wit n) (x.fitsink ∘ x.profile i o m v) := by
  let w:=x.wit n
  have hC : carried w (fun y=>dialed p x.l x.f y=x.q) :=
    normW_carried (subW_carried (spins p n) _)
  intro y hi
  refine hC y (fun h=>?_); apply hi
  refine ⟨?_,h, (role_scan p _ _ _ _).symm⟩
  intro j hj
  unfold profile; change scan p x.l x.f y j=0
  unfold scan
  simp [hj]
theorem refInk (i : Nodes) (o : UnitType p n N) (m:Mixer p n) (v : Ax p n d)
    (j:Fin r) : carried (x.reflected Y i o m v j) x.fitsink :=
  reflection_exact x Y i o m v j _ (rawink x m i o v)

end Appearance

theorem haze_small (w : Wgt (Fin r)) (δ : ℝ) (hδ : 0≤δ) :
    pr w (fun x=> w x < δ) ≤ r*δ := by
  classical
  unfold pr avg
  refine (Finset.sum_le_sum (s:=Finset.univ) (g:=fun _=>δ) (fun i _=>?_)).trans_eq (by simp)
  dsimp only
  by_cases h:w i<δ
  · rw [ind_one h,mul_one]; exact h.le
  rw [ind_zero h,mul_zero]; exact hδ

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
