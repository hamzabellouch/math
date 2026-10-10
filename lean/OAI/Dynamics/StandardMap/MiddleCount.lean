import OAI.Dynamics.StandardMap.ShapeTopology

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy

def bridgeMiddle (N : ℕ) : Finset ℕ := Finset.Icc (N/3+1) (2*N/3)
def MiddleLogGood (z : ℕ → ℝ) (N i : ℕ) : Prop :=
  (∀ j, j < i → (49/50:ℝ)*((i:ℝ)-(j:ℝ)) ≤ z i-z j) ∧
  (∀ j, i < j → j ≤ N → (49/50:ℝ)*((j:ℝ)-(i:ℝ)) ≤ z j-z i)
lemma bridgeMiddle_bounds (N i : ℕ) (hN : 100 ≤ N) (hi : i∈bridgeMiddle N) :
    2 ≤ i ∧ 2 ≤ N-i ∧ (N:ℝ)/3-1 ≤ (i:ℝ) ∧ (N:ℝ)/3-1 ≤ (N-i:ℕ) ∧ i ≤ N := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hi
  have hdiv := Nat.mod_lt N (by norm_num : 0 < 3)
  have hdiv' := Nat.mod_lt (2*N) (by norm_num : 0 < 3)
  have he := Nat.mod_add_div N 3
  have he' := Nat.mod_add_div (2*N) 3
  have h1 : 2 ≤ i := by omega
  have h2 : 2 ≤ N-i := by omega
  have h3 : N ≤ 3*i+2 := by omega
  have h4 : N ≤ 3*(N-i)+2 := by omega
  refine ⟨h1,h2,?_,?_,by omega⟩
  · have : (N:ℝ) ≤ 3*(i:ℝ)+2 := by exact_mod_cast h3
    linarith
  · have : (N:ℝ) ≤ 3*(N-i:ℕ)+2 := by exact_mod_cast h4
    linarith
lemma shortfall_count_sample (z : ℕ → ℝ) (c : ℝ) (hc : c < 1) (N : ℕ)
    (hz : ∀ j < N, z (j+1)-z j ≤ 1) (S : Finset ℕ)
    (hS : ∀ j∈S, 1 ≤ j ∧ j ≤ N ∧ ∃ l < j, z j-z l < c*((j:ℝ)-(l:ℝ))) :
    (S.card:ℝ) ≤ ((N:ℝ)-(z N-z 0))/(1-c) := by
  classical
  let D := (Finset.range N).filter fun j => ∃ l < j+1, z (j+1)-z l < c*((j+1:ℕ)-(l:ℝ))
  have hcard : S.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (fun j => j-1)
    · intro j hj
      obtain ⟨hj1,hjN,l,hl,hbad⟩ := hS j hj
      change j-1∈D
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega),l,by omega,?_⟩
      simpa only [Nat.sub_add_cancel hj1] using hbad
    · intro i hi j hj he
      have := (hS i hi).1
      have := (hS j hj).1
      dsimp only at he
      omega
  exact (Nat.cast_le.mpr hcard).trans (shortfall_count z c hc N hz)
noncomputable def bridgeMiddleGood (z : ℕ → ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (bridgeMiddle N).filter (MiddleLogGood z N)
lemma middle_log_good_count (z : ℕ → ℝ) (N : ℕ) (hN : 100 ≤ N)
    (hz : ∀ j < N, z (j+1)-z j ≤ 1)
    (htotal : (999/1000:ℝ)*(N:ℝ) ≤ z N-z 0) :
    (N:ℝ)/5 ≤ (bridgeMiddleGood z N).card := by
  classical
  change (N:ℝ)/5 ≤ ((bridgeMiddle N).filter (MiddleLogGood z N)).card
  let S := bridgeMiddle N
  let E := S.filter fun i => ∃ j < i, z i-z j < (49/50:ℝ)*((i:ℝ)-(j:ℝ))
  let F := S.filter fun i => ∃ j, i < j ∧ j ≤ N ∧ z j-z i < (49/50:ℝ)*((j:ℝ)-(i:ℝ))
  let zr : ℕ → ℝ := fun j => z N-z (N-j)
  have hE : (E.card:ℝ) ≤ ((N:ℝ)-(z N-z 0))/(1-(49/50:ℝ)) := by
    apply shortfall_count_sample z (49/50) (by norm_num) N hz E
    intro i hi
    obtain ⟨hi,hb⟩ := Finset.mem_filter.mp hi
    have hh := bridgeMiddle_bounds N i hN hi
    exact ⟨by omega,hh.2.2.2.2,hb⟩
  have hzr : ∀ j < N, zr (j+1)-zr j ≤ 1 := by
    intro j hj
    have hh := hz (N-j-1) (by omega)
    have he : N-j-1+1=N-j := by omega
    have he' : N-(j+1)=N-j-1 := by omega
    dsimp [zr]
    rw [he] at hh
    rw [he']
    linarith
  have hF : (F.card:ℝ) ≤ ((N:ℝ)-(z N-z 0))/(1-(49/50:ℝ)) := by
    let D := F.image (fun i => N-i)
    have hinj : Set.InjOn (fun i => N-i) (↑F : Set ℕ) := by
      intro i hi j hj he
      dsimp only at he
      have hiN := (bridgeMiddle_bounds N i hN (Finset.mem_filter.mp hi).1).2.2.2.2
      have hjN := (bridgeMiddle_bounds N j hN (Finset.mem_filter.mp hj).1).2.2.2.2
      omega
    have hcD : D.card=F.card := Finset.card_image_of_injOn hinj
    have hh := shortfall_count_sample zr (49/50) (by norm_num) N hzr D (by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hi,l,hil,hlN,hbad⟩ := Finset.mem_filter.mp hi
      have hiN := (bridgeMiddle_bounds N i hN hi).2.2.2.2
      have hi2 := (bridgeMiddle_bounds N i hN hi).2.1
      refine ⟨by omega,by omega,N-l,by omega,?_⟩
      dsimp [zr]
      rw [Nat.sub_sub_self hiN,Nat.sub_sub_self hlN,Nat.cast_sub hiN,Nat.cast_sub hlN]
      linarith)
    rw [hcD] at hh
    simpa [zr] using hh
  have hbad : S.filter (fun i => ¬MiddleLogGood z N i)=E∪F := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_union,MiddleLogGood,E,F,not_and_or,not_forall,not_le,exists_prop]
    exact and_or_left
  norm_num at hE hF
  have hcardE : (E.card:ℝ) ≤ (N:ℝ)/20 := by linarith
  have hcardF : (F.card:ℝ) ≤ (N:ℝ)/20 := by linarith
  have hcardbad : ((S.filter (fun i => ¬MiddleLogGood z N i)).card:ℝ) ≤ (N:ℝ)/10 := by
    rw [hbad]
    have hh : ((E∪F).card:ℝ) ≤ (E.card:ℝ)+(F.card:ℝ) := by exact_mod_cast Finset.card_union_le E F
    linarith
  have hScard : (N:ℝ)/3-2 ≤ (S.card:ℝ) := by
    have he : S.card=2*N/3-N/3 := by simp [S,bridgeMiddle,Nat.card_Icc]
    rw [he]
    have hx : N ≤ 3*(2*N/3-N/3)+6 := by omega
    have hx' : (N:ℝ) ≤ 3*(2*N/3-N/3:ℕ)+6 := by exact_mod_cast hx
    linarith
  have hpartition : ((S.filter (MiddleLogGood z N)).card:ℝ)+
      ((S.filter (fun i => ¬MiddleLogGood z N i)).card:ℝ)=(S.card:ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=S) (p:=MiddleLogGood z N)
  have hNN : (100:ℝ) ≤ N := by exact_mod_cast hN
  linarith
end StandardMapEntropy

end OAI
