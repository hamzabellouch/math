import OAI.Combinatorics.HadwigerCounterexample.ProjectionError

namespace OAI

/-! # Common Partitions -/

noncomputable section
namespace HadwigerCounterexample
open Finset Module Matrix Filter Function
open scoped BigOperators
variable {A B I J X : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J] [Fintype X]
variable (u : Wgt A) (w : Wgt I) (v : Wgt J)

set_option maxHeartbeats 800000 in
theorem rollup [Nonempty B] (hw : IsLaw w) (hv : IsLaw v) (hu : IsLaw u)
    (f : I×B→Wgt A) (g : J×B→Wgt A) (h k : I×J→ B) (R : ℝ) (hr : 0<R)
    (hg : ∀ i x, |g i x|≤R)
    (p : A→X) (ε : ℝ) (hx : wanes (pairW w unif) u f p ε) :
    avg (pairW w v) (fun i=> |rebate u (f (i.1,h i)) (g (i.2,k i)) p|) ≤
      num B ^ 2 * (R*ε) := by
  classical
  let H (i : I × B) (j : J × B) := |rebate u (f i) (g j) p|
  let T := num B
  have ht : 0<T := by unfold T num; positivity
  have he j :
      avg (pairW w (unif : Wgt B)) (fun i=> H i j)≤ R*ε := by
    let g' (i:A) := g j i/R
    have hh (i) : |g' i|≤1 := by
      unfold g'; rw [abs_div,abs_of_pos hr,div_le_one hr]; exact hg _ _
    have hz (i) :
        H i j=R* |dip u (fun x=> f i x-banner u p (f i) x) g'| := by
      unfold H; rw [rebate_calc _ _ _ _ hu.nz]
      unfold g' dip; simp_rw [←mul_div_assoc,avg_div]
      rw [abs_div,abs_of_pos hr]; field_simp
    simp_rw [hz,avg_mul']; exact mul_le_mul_of_nonneg_left (hx g' hh) hr.le
  have hh i j :
      H (i,h (i,j)) (j,k (i,j))≤ ∑ b : B,∑ c : B,H (i,b) (j,c) :=
    (Finset.single_le_sum (f:=fun x=> H (i,h (i,j)) (j,x)) (fun _ _ => abs_nonneg _) (mem_univ (k (i,j)))).trans
      (Finset.single_le_sum (f:=fun x => ∑ c:B,H (i,x) (j,c)) (fun _ _=> Finset.sum_nonneg (fun _ _=>abs_nonneg _)) (mem_univ (h (i,j))))
  have hi j c :
      avg w (fun i=>∑ b : B,H (i,b) (j,c))≤ T*(R*ε) := by
    have hg : ∀ i : I,(∑ b:B,H (i,b) (j,c))=T*avg unif (fun b=> H (i,b) (j,c)) := by
      intro i; simp only [avg,unif_apply,← Finset.mul_sum]
      change _ = T*(T⁻¹ * _)
      rw [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul]
    simp_rw [hg,avg_mul']
    refine mul_le_mul_of_nonneg_left ?_ ht.le; rw [← pairW_avg w unif (fun p : I×B=>H p (j,c))]
    exact he _
  change avg (pairW w v) _ ≤ T^2*(R*ε)
  rw [pairW_avg,avg_avg]
  refine hv.avg_le fun j=> ?_
  have hz i : ∑ b:B,∑ c:B,H (i,b) (j,c)=∑ c:B,∑ b:B,H (i,b) (j,c) :=
    Finset.sum_comm
  apply (avg_mono hw.nz (fun i => (hh i j).trans_eq (hz i))).trans
  rw [avg_sum]
  exact (Finset.sum_le_sum fun i _=>hi j i).trans_eq (by
    simp only [sum_const,nsmul_eq_mul,Finset.card_univ,T,num]; ring)

set_option maxHeartbeats 1200000 in
theorem global_net (R ε : ℝ) (hr : 0<R) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ r : ℕ,∃ l : ℕ,∀ (I J A : Type) [Fintype I] [Fintype J] [Fintype A]
      (w : Wgt I) (v : Wgt J) (u : Wgt A), IsLaw w→IsLaw v →IsLaw u →
      ∀ (P : I→Wgt A→Prop) (Q : J→Wgt A→Prop), (∀ i,roster (P i) r δ) →
        (∀ i,roster (Q i) r δ) →
        ∃ k : ℕ,k ≤ l∧ ∃ p:A→Fin k,
          ∀ f g:I × J→Wgt A,(∀ i,P i.1 (f i)) → (∀ i,Q i.2 (g i)) →
          avg (pairW w v) (fun i => |rebate u (mcut R u (f i)) (mcut R u (g i)) p|)≤ ε := by
  classical
  let δ := ε/(8*R)
  have hd : 0<δ := by positivity
  refine ⟨δ,hd,fun r=>?_⟩
  let B:=Fin (r+1); let t:=num B
  have ht : 0<t := by unfold t num; positivity
  let c:=ε/(2*(t^2)*R)
  have hc : 0<c := by positivity
  obtain ⟨l,hl⟩:= erosive R c hr.le hc
  refine ⟨l,fun I J A _ _ _ w v u hw hv hu P Q hp hq=>?_⟩
  choose s hs h1 using fun i=> roster_clip R u hu hr.le (P i) r δ (hp i)
  choose y hy h2 using fun i=> roster_clip R u hu hr.le (Q i) r δ (hq i)
  let F : I×B→Wgt A := uncurry s
  let G : J×B→Wgt A := uncurry y
  obtain ⟨m,hm,p,hP⟩:= hl A (I×B) (pairW w unif) u F (pairW_law hw unif_law) hu (fun i j=> hs _ _ _)
  refine ⟨m,hm,p,fun f g hf hg=>?_⟩
  let f' (i : I×J):= mcut R u (f i)
  let g' (i : I×J):= mcut R u (g i)
  choose a hA using fun i:I×J => h1 i.1 (f i) (hf i)
  choose b hB using fun i:I×J => h2 i.2 (g i) (hg i)
  let H (i:I×J) := |rebate u (F (i.1,a i)) (G (i.2,b i)) p|
  let D:=pairW w v; have hD:= pairW_law hw hv
  have he := rollup u w v hw hv hu F G a b R hr (fun i j=> hy _ _ _) p c hP
  have hb : 0≤2*R := by linarith only [hr]
  have hi (i:I×J) : |rebate u (f' i) (g' i) p|≤ H i+(δ*(4*R)) := by
    let A' := F (i.1,a i); let B' := G (i.2,b i)
    have h1 (j) : |g' i j|≤R := by
      rw [abs_of_nonneg ((mcut_range _ _ _ hr.le j).1)]
      exact (mcut_range _ _ _ hr.le j).2
    have h3 : |rebate u (f' i) (g' i) p - rebate u A' (g' i) p|≤ δ*(2*R) := by
      exact (rebate_cost u _ _ A' p hu.nz R hr.le h1).trans (mul_le_mul_of_nonneg_right (hA i) hb)
    have h4 : |rebate u A' (g' i) p - rebate u A' B' p|≤δ*(2*R) := by
      rw [rebate_sym u A',rebate_sym u A']
      exact (rebate_cost u _ _ B' p hu.nz R hr.le (fun i=>hs _ _ _)).trans
        (mul_le_mul_of_nonneg_right (hB i) hb)
    let U:=rebate u A' B' p
    let X:=rebate u (f' i) (g' i) p
    have hz:= (abs_sub_le X (rebate u A' (g' i) p) U).trans (add_le_add h3 h4)
    calc |X| = |(X-U)+U| := by rw [sub_add_cancel]
         _ ≤ _ := ((abs_add_le _ _).trans (add_le_add_left hz _)).trans_eq (by
           change _+ |U| = |U|+δ*(4*R)
           ring)
  refine (avg_mono hD.nz hi).trans ?_
  rw [avg_add,hD.avg_const]
  exact (add_le_add_left he _).trans_eq (by
    change t^2*(R*c)+δ*(4*R)=_
    unfold δ c; field_simp; ring)
end HadwigerCounterexample

end

end OAI
