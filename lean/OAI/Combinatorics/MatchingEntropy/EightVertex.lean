import OAI.Combinatorics.MatchingEntropy.KleeSharpness

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

def obstructionGraph : LooplessGraph (Fin 8) (Fin 12) where
  left := ![0,0,0,1,1,2,2,2,3,5,5,6]
  right := ![1,3,5,4,6,3,4,7,4,6,7,7]
  loopless := by intro e; fin_cases e <;> decide

def obstructionEdges (i : Fin 5) : Finset (Fin 12) :=
  ![{0,7,8,9}, {1,4,6,10}, {2,3,5,11}, {1,3,7,9}, {2,4,7,8}] i

def obstructionUniform : Fin 12 → ℝ := fun _ => 1 / 3

def obstructionLaw : obstructionGraph.Matching → ℝ :=
  fun M => ∑ i : Fin 3, if M.val = obstructionEdges i.castSucc.castSucc then 1 / 3 else 0

theorem obstruction_simple : IsSimpleLabelled obstructionGraph := by
  unfold IsSimpleLabelled obstructionGraph
  decide

theorem obstruction_matching (i : Fin 5) : obstructionGraph.IsPerfectMatching (obstructionEdges i) := by
  unfold LooplessGraph.IsPerfectMatching LooplessGraph.Incident obstructionGraph ExistsUnique
  fin_cases i <;> decide

def obstructionMatching (i : Fin 5) : obstructionGraph.Matching := ⟨obstructionEdges i,obstruction_matching i⟩

theorem obstructionEdges_injective : Function.Injective obstructionEdges := by
  unfold Function.Injective obstructionEdges
  decide

theorem obstructionMatching_injective : Function.Injective obstructionMatching := by
  intro i j h
  exact obstructionEdges_injective (congrArg Subtype.val h)

theorem obstruction_binary_classify (a b c d e f g h i j k l : ℕ)
    (h0 : a+b+c=1) (h1 : a+d+e=1) (h2 : f+g+h=1) (h3 : b+f+i=1)
    (h4 : d+g+i=1) (h5 : c+j+k=1) (h6 : e+j+l=1) (h7 : h+k+l=1) :
    (a=1 ∧ b=0 ∧ c=0 ∧ d=0 ∧ e=0 ∧ f=0 ∧ g=0 ∧ h=1 ∧ i=1 ∧ j=1 ∧ k=0 ∧ l=0) ∨
    (a=0 ∧ b=1 ∧ c=0 ∧ d=0 ∧ e=1 ∧ f=0 ∧ g=1 ∧ h=0 ∧ i=0 ∧ j=0 ∧ k=1 ∧ l=0) ∨
    (a=0 ∧ b=0 ∧ c=1 ∧ d=1 ∧ e=0 ∧ f=1 ∧ g=0 ∧ h=0 ∧ i=0 ∧ j=0 ∧ k=0 ∧ l=1) ∨
    (a=0 ∧ b=1 ∧ c=0 ∧ d=1 ∧ e=0 ∧ f=0 ∧ g=0 ∧ h=1 ∧ i=0 ∧ j=1 ∧ k=0 ∧ l=0) ∨
    (a=0 ∧ b=0 ∧ c=1 ∧ d=0 ∧ e=1 ∧ f=0 ∧ g=0 ∧ h=1 ∧ i=1 ∧ j=0 ∧ k=0 ∧ l=0) := by
  rcases (show a = 1 ∨ b = 1 ∨ c = 1 by omega) with ha | hb | hc
  · left
    omega
  · rcases (show d = 0 ∨ d = 1 by omega) with hd | hd
    · right; left; omega
    · right; right; right; left; omega
  · rcases (show d = 0 ∨ d = 1 by omega) with hd | hd
    · right; right; right; right; omega
    · right; right; left; omega

theorem obstruction_classify (M : obstructionGraph.Matching) : ∃ i : Fin 5, M = obstructionMatching i := by
  let a : Fin 12 → ℕ := fun e => if e ∈ M.val then 1 else 0
  have hadeg (v : Fin 8) : (∑ e : Fin 12, if obstructionGraph.Incident v e then a e else 0) = 1 := by
    obtain ⟨e,he,hu⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [he,a]
    · intro f _ hfe
      by_cases hf : obstructionGraph.Incident v f
      · have hfm : f ∉ M.val := fun h => hfe (hu f ⟨h,hf⟩)
        simp [hf,a,hfm]
      · simp [hf]
    · simp
  have h0 := hadeg 0
  have h1 := hadeg 1
  have h2 := hadeg 2
  have h3 := hadeg 3
  have h4 := hadeg 4
  have h5 := hadeg 5
  have h6 := hadeg 6
  have h7 := hadeg 7
  simp +decide [obstructionGraph,LooplessGraph.Incident,Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  have hcases := obstruction_binary_classify (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)
    (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  clear hadeg h0 h1 h2 h3 h4 h5 h6 h7
  rcases hcases with hh | hh | hh | hh | hh
  all_goals simp [a] at hh
  · refine ⟨0,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide
  · refine ⟨1,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide
  · refine ⟨2,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide
  · refine ⟨3,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide
  · refine ⟨4,Subtype.ext ?_⟩
    ext e
    fin_cases e <;> simp_all +decide

def obstructionEquiv : Fin 5 ≃ obstructionGraph.Matching :=
  Equiv.ofBijective obstructionMatching ⟨obstructionMatching_injective,
    fun M => by obtain ⟨i,hi⟩ := obstruction_classify M; exact ⟨i,hi.symm⟩⟩

def obstructionSelected (i : Fin 3) : obstructionGraph.Matching :=
  obstructionMatching (i.castSucc.castSucc)

theorem obstructionSelected_injective : Function.Injective obstructionSelected := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 5 => k.val) (obstructionMatching_injective h))

theorem obstruction_law_eq_fiber :
    obstructionLaw = fiberMass (uniformLaw (Fin 3)) obstructionSelected := by
  ext M
  unfold obstructionLaw fiberMass
  apply Finset.sum_congr rfl
  intro i _
  have he : obstructionSelected i = M ↔ M.val = obstructionEdges i.castSucc.castSucc := by
    rw [Subtype.ext_iff]
    exact eq_comm
  simp [he,uniformLaw]

theorem obstruction_law_mean : obstructionGraph.mean obstructionLaw = obstructionUniform := by
  ext e
  rw [obstruction_law_eq_fiber,LooplessGraph.mean,fiberMass_expect]
  fin_cases e <;> simp +decide [obstructionSelected,obstructionMatching,obstructionEdges,
    uniformLaw,LooplessGraph.indicator,obstructionUniform,Fin.sum_univ_succ]

theorem obstruction_law_feasible : obstructionLaw ∈ obstructionGraph.feasibleLaws obstructionUniform := by
  refine ⟨?_,obstruction_law_mean⟩
  rw [obstruction_law_eq_fiber]
  exact fiberMass_mem_simplex uniformLaw_simplex _

theorem obstruction_uniform_mem : obstructionUniform ∈ obstructionGraph.polytope :=
  (obstructionGraph.mem_polytope_iff _).mpr ⟨_,obstruction_law_feasible⟩

theorem obstruction_mean_coordinates (p : obstructionGraph.Matching → ℝ) :
    obstructionGraph.mean p =
      ![p (obstructionMatching 0), p (obstructionMatching 1) + p (obstructionMatching 3),
        p (obstructionMatching 2) + p (obstructionMatching 4),
        p (obstructionMatching 2) + p (obstructionMatching 3),
        p (obstructionMatching 1) + p (obstructionMatching 4),
        p (obstructionMatching 2), p (obstructionMatching 1),
        p (obstructionMatching 0) + p (obstructionMatching 3) + p (obstructionMatching 4),
        p (obstructionMatching 0) + p (obstructionMatching 4),
        p (obstructionMatching 0) + p (obstructionMatching 3),
        p (obstructionMatching 1), p (obstructionMatching 2)] := by
  ext e
  unfold LooplessGraph.mean
  rw [← Equiv.sum_comp obstructionEquiv]
  change (∑ i : Fin 5, p (obstructionMatching i) * obstructionGraph.indicator (obstructionMatching i) e) = _
  fin_cases e <;> simp +decide [LooplessGraph.indicator,obstructionMatching,obstructionEdges,Fin.sum_univ_succ,add_assoc]

theorem obstruction_law_values (i : Fin 5) :
    obstructionLaw (obstructionMatching i) = ![(1 : ℝ)/3,1/3,1/3,0,0] i := by
  fin_cases i <;> simp +decide [obstructionLaw,obstructionMatching,obstructionEdges,Fin.sum_univ_succ]

theorem obstruction_unique_law :
    obstructionGraph.feasibleLaws obstructionUniform = {obstructionLaw} := by
  apply Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr obstruction_law_feasible)
  intro p hp
  have hm := hp.2
  rw [obstruction_mean_coordinates] at hm
  have h0 := congrFun hm 0
  have h1 := congrFun hm 6
  have h2 := congrFun hm 5
  have h3 := congrFun hm 3
  have h4 := congrFun hm 4
  change p (obstructionMatching 0) = 1/3 at h0
  change p (obstructionMatching 1) = 1/3 at h1
  change p (obstructionMatching 2) = 1/3 at h2
  change p (obstructionMatching 2) + p (obstructionMatching 3) = 1/3 at h3
  change p (obstructionMatching 1) + p (obstructionMatching 4) = 1/3 at h4
  apply Set.mem_singleton_iff.mpr
  ext M
  obtain ⟨i,rfl⟩ := obstruction_classify M
  rw [obstruction_law_values]
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change p (obstructionMatching 3) = 0
    linarith only [h2,h3]
  · change p (obstructionMatching 4) = 0
    linarith only [h1,h4]

theorem obstruction_entropy_law : entropy obstructionLaw = Real.log 3 := by
  rw [obstruction_law_eq_fiber,entropy_fiberMass_injective _ _ obstructionSelected_injective,uniformLaw_entropy]
  norm_num

theorem obstruction_maxEntropy : maxMatchingEntropy obstructionGraph obstructionUniform = Real.log 3 := by
  obtain ⟨p,hp,he⟩ := maxMatchingEntropy_attained _ obstruction_uniform_mem
  rw [obstruction_unique_law,Set.mem_singleton_iff] at hp
  rw [← he,hp,obstruction_entropy_law]

theorem obstruction_entropy_terms :
    entropy obstructionUniform = 4 * Real.log 3 ∧
    complementEntropy obstructionUniform = 8 * Real.log (3/2) := by
  have hF : Real.negMulLog (1/3) = Real.log 3 / 3 := by
    norm_num [Real.negMulLog,Real.log_div]
    ring
  have hB : Real.negMulLog (1-1/3) = (2/3) * Real.log (3/2) := by
    norm_num [Real.negMulLog,Real.log_div]
    ring
  constructor
  · simp only [entropy,obstructionUniform,hF,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  · change (∑ _ : Fin 12, Real.negMulLog (1-1/3)) = _
    simp only [hB,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring

theorem obstruction_logarithms :
    entropy obstructionUniform - complementEntropy obstructionUniform = 4 * Real.log (4/3) ∧
    entropy obstructionUniform - complementEntropy obstructionUniform -
      maxMatchingEntropy obstructionGraph obstructionUniform = Real.log (256/243) := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1
    norm_num
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 8 using 1
    norm_num
  have h243 : Real.log 243 = 5 * Real.log 3 := by
    convert Real.log_pow (3 : ℝ) 5 using 1
    norm_num
  rw [obstruction_entropy_terms.1,obstruction_entropy_terms.2,obstruction_maxEntropy]
  norm_num [Real.log_div,h4,h256,h243]
  constructor <;> ring

theorem eight_vertex_obstruction :
    IsSimpleLabelled obstructionGraph ∧
    (∀ M : obstructionGraph.Matching, ∃! i : Fin 5, M.val = obstructionEdges i) ∧
    (∀ i : Fin 5, obstructionGraph.IsPerfectMatching (obstructionEdges i)) ∧
    Fintype.card obstructionGraph.Matching = 5 ∧
    obstructionUniform ∈ obstructionGraph.polytope ∧
    obstructionGraph.feasibleLaws obstructionUniform = {obstructionLaw} ∧
    maxMatchingEntropy obstructionGraph obstructionUniform = Real.log 3 ∧
    entropy obstructionUniform - complementEntropy obstructionUniform = 4 * Real.log (4 / 3) ∧
    entropy obstructionUniform - complementEntropy obstructionUniform -
      maxMatchingEntropy obstructionGraph obstructionUniform = Real.log (256 / 243) ∧
    0 < Real.log (256 / 243) := by
  refine ⟨obstruction_simple,?_,obstruction_matching,?_,obstruction_uniform_mem,
    obstruction_unique_law,obstruction_maxEntropy,obstruction_logarithms.1,
    obstruction_logarithms.2,Real.log_pos (by norm_num)⟩
  · intro M
    obtain ⟨i,rfl⟩ := obstruction_classify M
    refine ⟨i,rfl,?_⟩
    intro j hj
    exact (obstructionEdges_injective hj).symm
  · exact (Fintype.card_congr obstructionEquiv).symm.trans (Fintype.card_fin 5)

end MatchingEntropyBounds.Refined

end

end OAI
