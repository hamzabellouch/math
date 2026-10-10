import Mathlib

namespace OAI

                                          
section

                                                                            
                                                                                
namespace UniformKServer.RankSuperadditivity
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

structure Input (Ω ι : Type*) [Fintype Ω] [Fintype ι] (k : ℕ) where
  μ : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ μ ω
  total : ∑ ω, μ ω = 1
  N : Ω → ι → ℕ
  bound : ∀ ω, ∑ i, N ω i ≤ k

def countRank (μ : Ω → ℝ) (N : Ω → ℕ) (a : ℕ) : ℝ :=
  ∑ ω, μ ω * if N ω ≤ a then 1 else 0

def rankSum (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range k, f (countRank μ N a)


def hinge (b x : ℝ) : ℝ := max (b-x) 0

def interpolate (c d : ℝ) (L : List (ℝ × ℝ)) (x : ℝ) : ℝ :=
  c + d*x + (L.map (fun p => p.2 * hinge p.1 x)).sum

theorem interpolate_cons (c d : ℝ) (L : List (ℝ × ℝ)) (t w x : ℝ) :
    interpolate c d ((t,w)::L) x = interpolate c d L x + w*hinge t x := by
  simp [interpolate]; ring

theorem finite_convex_interpolation_aux (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f) (l : List ℝ)
    (hs : l.Pairwise (· < ·)) (hmem : ∀ x ∈ l, x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c d : ℝ, ∃ W : List (ℝ × ℝ),
      (∀ p ∈ W, 0 ≤ p.2) ∧ (∀ x ∈ l, f x = interpolate c d W x) ∧
      (∀ a b rest, l = a::b::rest → ∀ x, x ≤ a →
        interpolate c d W x = f a + ((f b-f a)/(b-a))*(x-a)) := by
  induction l with
  | nil =>
      refine ⟨0,0,[],by simp,by simp,?_⟩
      intro a b rest he; cases he
  | cons a l ih =>
      cases l with
      | nil =>
          refine ⟨f a,0,[],by simp,?_,?_⟩
          · simp [interpolate]
          · intro a' b rest he; cases he
      | cons b rest =>
          have hab : a < b := (List.pairwise_cons.mp hs).1 _ (by simp)
          have htail := (List.pairwise_cons.mp hs).2
          have hmTail : ∀ x ∈ b::rest, x ∈ Set.Icc (0 : ℝ) 1 :=
            fun x hx => hmem x (by simp [hx])
          have hid : ((f b-f a)/(b-a))*(b-a) = f b-f a :=
            div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')
          cases rest with
          | nil =>
              refine ⟨f a-((f b-f a)/(b-a))*a, (f b-f a)/(b-a), [],by simp,?_,?_⟩
              · intro x hx
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl <;> simp only [interpolate, List.map_nil, List.sum_nil, add_zero]
                · ring
                · nlinarith [hid]
              · intro a' b' rest he x hx
                cases he
                simp only [interpolate, List.map_nil, List.sum_nil, add_zero]
                ring
          | cons b' rest =>
              obtain ⟨c,d,W,hW,heq,hleft⟩ := ih htail hmTail
              have hbb : b < b' := (List.pairwise_cons.mp htail).1 _ (by simp)
              let δ := (f b'-f b)/(b'-b) - (f b-f a)/(b-a)
              have hδ : 0 ≤ δ := sub_nonneg.mpr (hf.slope_mono_adjacent
                (hmem a (by simp)) (hmem b' (by simp)) hab hbb)
              refine ⟨c,d,(b,δ)::W,?_,?_,?_⟩
              · intro p hp
                simp only [List.mem_cons] at hp
                rcases hp with rfl | hp
                · exact hδ
                · exact hW p hp
              · intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · rw [interpolate_cons, hleft b b' rest rfl x hab.le]
                  rw [hinge, max_eq_left (sub_nonneg.mpr hab.le)]
                  dsimp only [δ]
                  nlinarith [hid]
                · have hbx : b ≤ x := by
                    rcases hx with rfl | hx
                    · exact le_rfl
                    · exact ((List.pairwise_cons.mp htail).1 x (by simpa using hx)).le
                  rw [interpolate_cons, ← heq x (by simp only [List.mem_cons]; exact hx)]
                  simp [hinge, max_eq_right (sub_nonpos.mpr hbx)]
              · intro a' b'' rest' hlist x hx
                cases hlist
                rw [interpolate_cons, hleft b b' rest rfl x (hx.trans hab.le)]
                rw [hinge, max_eq_left (sub_nonneg.mpr (hx.trans hab.le))]
                dsimp only [δ]
                nlinarith [hid]

theorem finite_convex_interpolation (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f) (S : Finset ℝ)
    (hS : ∀ x ∈ S, x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c d : ℝ, ∃ W : List (ℝ × ℝ),
      (∀ p ∈ W, 0 ≤ p.2) ∧ (∀ x ∈ S, f x = interpolate c d W x) := by
  classical
  obtain ⟨c,d,W,hW,heq,_⟩ := finite_convex_interpolation_aux f hf (S.sort (· ≤ ·))
    S.sortedLT_sort.pairwise (by simpa using hS)
  exact ⟨c,d,W,hW,by simpa using heq⟩


theorem countRank_bounds {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ) (a : ℕ) :
    countRank I.μ N a ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun ω _ => mul_nonneg (I.nonneg ω) (by split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ ω, I.μ ω := Finset.sum_le_sum fun ω _ => by
        split_ifs <;> simp [I.nonneg ω]
      _ = 1 := I.total

theorem countRank_one {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ) (a : ℕ)
    (hN : ∀ ω, N ω ≤ a) : countRank I.μ N a = 1 := by
  simpa [countRank, hN] using I.total

theorem indicator_count (n m : ℕ) :
    (∑ a ∈ Finset.range n, if m ≤ a then (1 : ℕ) else 0) = n-m := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      split_ifs <;> omega

theorem indicator_count_real (n m : ℕ) :
    (∑ a ∈ Finset.range n, if m ≤ a then (1 : ℝ) else 0) = max ((n : ℝ)-(m : ℝ)) 0 := by
  have he : (∑ a ∈ Finset.range n, if m ≤ a then (1 : ℝ) else 0) = ((n-m : ℕ) : ℝ) := by
    exact_mod_cast indicator_count n m
  rw [he]
  by_cases h : m ≤ n
  · rw [Nat.cast_sub h, max_eq_left (sub_nonneg.mpr (by exact_mod_cast h))]
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    simp only [Nat.cast_zero]
    exact (max_eq_right (sub_nonpos.mpr (by exact_mod_cast (show n ≤ m by omega)))).symm

def deficit (μ : Ω → ℝ) (N : Ω → ℕ) (n : ℕ) : ℝ :=
  ∑ ω, μ ω * max ((n : ℝ)-(N ω : ℝ)) 0

theorem deficit_eq_sum_rank (μ : Ω → ℝ) (N : Ω → ℕ) (n : ℕ) :
    deficit μ N n = ∑ a ∈ Finset.range n, countRank μ N a := by
  simp only [deficit, ← indicator_count_real, Finset.mul_sum, countRank]
  rw [Finset.sum_comm]

theorem selected_count_lower (A : Finset ℕ) (m : ℕ) :
    max ((A.card : ℝ) - (m : ℝ)) 0 ≤ ∑ a ∈ A, if m ≤ a then (1 : ℝ) else 0 := by
  classical
  have hc := Finset.card_filter_add_card_filter_not (s := A) (p := fun a => m ≤ a)
  have hle : (A.filter (fun a => ¬ m ≤ a)).card ≤ m := by
    calc
      _ ≤ (Finset.range m).card := Finset.card_le_card fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
        omega
      _ = m := Finset.card_range _
  have hn : A.card ≤ m + (A.filter (fun a => m ≤ a)).card := by omega
  rw [Finset.sum_boole]
  apply max_le
  · have hn' : (A.card : ℝ) ≤ (m : ℝ) + ((A.filter (fun a => m ≤ a)).card : ℝ) := by exact_mod_cast hn
    linarith
  · positivity

theorem selected_rank_lower {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ) (A : Finset ℕ) :
    deficit I.μ N A.card ≤ ∑ a ∈ A, countRank I.μ N a := by
  unfold deficit countRank
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun ω _ => by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (selected_count_lower A (N ω)) (I.nonneg ω)

noncomputable def activeRanks (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (b : ℝ) : Finset ℕ :=
  (Finset.range k).filter (fun a => countRank μ N a < b)

theorem hinge_selection (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (b : ℝ) :
    rankSum μ N k (hinge b) = (activeRanks μ N k b).card*b -
      ∑ a ∈ activeRanks μ N k b, countRank μ N a := by
  classical
  have he : ∀ a, hinge b (countRank μ N a) =
      if countRank μ N a < b then b-countRank μ N a else 0 := by
    intro a
    split_ifs with h
    · exact max_eq_left (sub_nonneg.mpr h.le)
    · exact max_eq_right (sub_nonpos.mpr (by linarith))
  simp only [rankSum, he, ← Finset.sum_filter]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, activeRanks]

theorem hinge_dual {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ)
    (hN : ∀ ω, N ω ≤ k) (b : ℝ) (hb : b ≤ 1) (n : ℕ) :
    (n : ℝ)*b - deficit I.μ N n ≤ rankSum I.μ N k (hinge b) := by
  have hfirst : (n : ℝ)*b - deficit I.μ N n ≤ rankSum I.μ N n (hinge b) := by
    rw [deficit_eq_sum_rank]
    calc
      _ = ∑ a ∈ Finset.range n, (b-countRank I.μ N a) := by simp [Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum fun a _ => le_max_left _ _
  apply hfirst.trans
  dsimp [rankSum]
  by_cases hnk : n ≤ k
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnk) (fun a _ _ => le_max_right _ _)
  · have hkn : k ≤ n := by omega
    apply le_of_eq
    symm
    apply Finset.sum_subset (Finset.range_mono hkn)
    intro a ha hnot
    have hka : k ≤ a := by simpa only [Finset.mem_range, not_lt] using hnot
    rw [countRank_one I N a (fun ω => (hN ω).trans hka)]
    exact max_eq_right (sub_nonpos.mpr hb)

theorem deficit_subadditive {k : ℕ} (I : Input Ω ι k) (n : ι → ℕ) :
    deficit I.μ (fun ω => ∑ i, I.N ω i) (∑ i, n i) ≤
      ∑ i, deficit I.μ (fun ω => I.N ω i) (n i) := by
  simp only [deficit]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (I.nonneg ω)
  apply max_le
  · simp only [Nat.cast_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => le_max_left _ _
  · exact Finset.sum_nonneg fun i _ => le_max_right _ _

theorem hinge_superadditivity {k : ℕ} (I : Input Ω ι k) (b : ℝ) (hb : b ≤ 1) :
    (∑ i, rankSum I.μ (fun ω => I.N ω i) k (hinge b)) ≤
      rankSum I.μ (fun ω => ∑ i, I.N ω i) k (hinge b) := by
  let n : ι → ℕ := fun i => (activeRanks I.μ (fun ω => I.N ω i) k b).card
  have hchild (i : ι) : rankSum I.μ (fun ω => I.N ω i) k (hinge b) ≤
      (n i : ℝ)*b - deficit I.μ (fun ω => I.N ω i) (n i) := by
    rw [hinge_selection]
    exact sub_le_sub_left (selected_rank_lower I _ _) _
  calc
    _ ≤ ∑ i, ((n i : ℝ)*b - deficit I.μ (fun ω => I.N ω i) (n i)) :=
      Finset.sum_le_sum fun i _ => hchild i
    _ = (∑ i, n i : ℕ)*b - ∑ i, deficit I.μ (fun ω => I.N ω i) (n i) := by
      simp [Finset.sum_sub_distrib, Finset.sum_mul]
    _ ≤ (∑ i, n i : ℕ)*b - deficit I.μ (fun ω => ∑ i, I.N ω i) (∑ i, n i) :=
      sub_le_sub_left (deficit_subadditive I n) _
    _ ≤ _ := hinge_dual I _ I.bound b hb _


def mean (μ : Ω → ℝ) (N : Ω → ℕ) : ℝ := ∑ ω, μ ω * (N ω : ℝ)
def risk (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  rankSum μ N k f - (k : ℝ)*f 1

theorem sum_rank_eq {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ)
    (hN : ∀ ω, N ω ≤ k) :
    (∑ a ∈ Finset.range k, countRank I.μ N a) = (k : ℝ) - mean I.μ N := by
  rw [← deficit_eq_sum_rank]
  simp only [deficit, max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr (hN _))),
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, I.total, one_mul, mean]

theorem component_bound {k : ℕ} (I : Input Ω ι k) (i : ι) (ω : Ω) : I.N ω i ≤ k := by
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans (I.bound ω)

theorem mean_parent {k : ℕ} (I : Input Ω ι k) :
    mean I.μ (fun ω => ∑ i, I.N ω i) = ∑ i, mean I.μ (fun ω => I.N ω i) := by
  simp only [mean, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem risk_hinge_large {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ)
    (hN : ∀ ω, N ω ≤ k) (b : ℝ) (hb : 1 ≤ b) : risk I.μ N k (hinge b) = mean I.μ N := by
  have hp (a : ℕ) : hinge b (countRank I.μ N a) = b-countRank I.μ N a :=
    max_eq_left (sub_nonneg.mpr ((countRank_bounds I N a).2.trans hb))
  simp only [risk, rankSum]
  simp_rw [hp]
  simp only [hinge, max_eq_left (sub_nonneg.mpr hb), Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [sum_rank_eq I N hN]
  ring

theorem risk_hinge_superadditive {k : ℕ} (I : Input Ω ι k) (b : ℝ) :
    (∑ i, risk I.μ (fun ω => I.N ω i) k (hinge b)) ≤
      risk I.μ (fun ω => ∑ i, I.N ω i) k (hinge b) := by
  rcases le_total b 1 with hb | hb
  · simpa only [risk, hinge, max_eq_right (sub_nonpos.mpr hb), mul_zero, sub_zero]
      using hinge_superadditivity I b hb
  · simp_rw [risk_hinge_large I _ (component_bound I _) b hb]
    rw [risk_hinge_large I _ I.bound b hb, mean_parent]

theorem risk_congr {k : ℕ} (μ : Ω → ℝ) (N : Ω → ℕ) {f g : ℝ → ℝ}
    (h : ∀ a < k, f (countRank μ N a) = g (countRank μ N a)) (h1 : f 1 = g 1) :
    risk μ N k f = risk μ N k g := by
  unfold risk rankSum
  rw [h1]
  congr 1
  exact Finset.sum_congr rfl fun a ha => h a (Finset.mem_range.mp ha)

theorem risk_add (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (f g : ℝ → ℝ) :
    risk μ N k (fun x => f x+g x) = risk μ N k f + risk μ N k g := by
  simp only [risk, rankSum, Finset.sum_add_distrib]
  ring

theorem risk_smul (μ : Ω → ℝ) (N : Ω → ℕ) (k : ℕ) (w : ℝ) (f : ℝ → ℝ) :
    risk μ N k (fun x => w*f x) = w*risk μ N k f := by
  simp only [risk, rankSum, ← Finset.mul_sum]
  ring

theorem risk_affine {k : ℕ} (I : Input Ω ι k) (N : Ω → ℕ)
    (hN : ∀ ω, N ω ≤ k) (c d : ℝ) :
    risk I.μ N k (fun x => c+d*x) = -d*mean I.μ N := by
  simp only [risk, rankSum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  rw [sum_rank_eq I N hN]
  ring

theorem interpolation_superadditive {k : ℕ} (I : Input Ω ι k)
    (c d : ℝ) (W : List (ℝ × ℝ)) (hW : ∀ p ∈ W, 0 ≤ p.2) :
    (∑ i, risk I.μ (fun ω => I.N ω i) k (interpolate c d W)) ≤
      risk I.μ (fun ω => ∑ i, I.N ω i) k (interpolate c d W) := by
  induction W with
  | nil =>
      have he : interpolate c d [] = (fun x => c+d*x) := by funext x; simp [interpolate]
      rw [he]
      simp_rw [risk_affine I _ (component_bound I _) c d]
      rw [risk_affine I _ I.bound c d, mean_parent, Finset.mul_sum]
  | cons p W ih =>
      have hp : 0 ≤ p.2 := hW p (by simp)
      have ht : ∀ q ∈ W, 0 ≤ q.2 := fun q hq => hW q (by simp [hq])
      have he : interpolate c d (p::W) = (fun x => interpolate c d W x + p.2*hinge p.1 x) := by
        funext x; exact interpolate_cons c d W p.1 p.2 x
      simp_rw [he, risk_add, risk_smul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      exact add_le_add (ih ht) (mul_le_mul_of_nonneg_left (risk_hinge_superadditive I p.1) hp)

theorem rank_superadditivity {k : ℕ} (I : Input Ω ι k) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f) (h1 : f 1 = 0) :
    (∑ i, rankSum I.μ (fun ω => I.N ω i) k f) ≤
      rankSum I.μ (fun ω => ∑ i, I.N ω i) k f := by
  classical
  let N : Option ι → Ω → ℕ := fun j ω => match j with
    | none => ∑ i, I.N ω i
    | some i => I.N ω i
  let S : Finset ℝ := insert 1 ((Finset.univ : Finset (Option ι × Fin k)).image
    (fun q => countRank I.μ (N q.1) q.2))
  have hS : ∀ x ∈ S, x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
    rcases hx with rfl | ⟨q,rfl⟩
    · exact ⟨by norm_num, le_rfl⟩
    · exact countRank_bounds I _ _
  obtain ⟨c,d,W,hW,heq⟩ := finite_convex_interpolation f hf S hS
  have hEq (j : Option ι) : risk I.μ (N j) k f = risk I.μ (N j) k (interpolate c d W) := by
    apply risk_congr I.μ (N j)
    · intro a ha
      apply heq
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨(j,⟨a,ha⟩),Finset.mem_univ _,rfl⟩
    · exact heq 1 (Finset.mem_insert_self _ _)
  have hineq := interpolation_superadditive I c d W hW
  have hchild (i : ι) := hEq (some i)
  have hpar := hEq none
  dsimp only [N] at hchild hpar
  simp_rw [← hchild] at hineq
  rw [← hpar] at hineq
  simpa only [risk, h1, mul_zero, sub_zero] using hineq

end UniformKServer.RankSuperadditivity

end



end OAI
