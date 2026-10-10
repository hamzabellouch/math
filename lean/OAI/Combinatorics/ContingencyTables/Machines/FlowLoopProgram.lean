import OAI.Combinatorics.ContingencyTables.Transport.FlowMatrixBounds

namespace OAI

/-! # Polynomial binary execution of the bounded residual-flow loop -/

namespace ContingencyTables.FlowLoopProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram FlowMatrixBounds

abbrev Context := NatMatrix×(ℕ×ℕ)
abbrev State := Context×FlowMatrix

def step (z : ℕ×State) : State :=
  (z.2.1,FlowMatrixProgram.advance ((z.2.1.1,z.2.2),z.2.1.2))

def stepRealizer : Realizer step :=
  pair (composition second first)
    (composition (pair (pair (composition (composition second first) first)
      (composition second second)) (composition (composition second first) second))
      FlowMatrixProgram.advanceRealizer)

lemma polynomial_step : PolynomialTime stepRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_first) (polynomial_composition polynomial_second polynomial_second))
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_second)) FlowMatrixProgram.polynomial_advance)

lemma fold_context (steps : List ℕ) (s : State) :
    (steps.foldl (fun s i=>step (i,s)) s).1=s.1 := by
  induction steps generalizing s with
  | nil => rfl
  | cons i steps ih => exact ih (step (i,s))

lemma fold_weight (steps : List ℕ) (s : State) :
    weight (steps.foldl (fun s i=>step (i,s)) s).2≤
      max (weight s.2) (matrixBound s.1.1) := by
  induction steps generalizing s with
  | nil => exact le_max_left _ _
  | cons i steps ih =>
    have ht := ih (step (i,s))
    have hs := advance_weight ((s.1.1,s.2),s.1.2)
    exact ht.trans (max_le hs (le_max_right _ _))

theorem polynomial_loop : PolynomialTime (MatchingFPRAS.TreeTyped.fold stepRealizer) := by
  apply polynomial_fold polynomial_step (20*(X+1)^3)
  intro steps s pre _post _he
  let S := weight (steps,s)
  let out := pre.foldl (fun s i=>step (i,s)) s
  have hs : weight s≤ S := weight_snd (steps,s)
  have hc : weight s.1≤ S := (weight_fst s).trans hs
  have hC : weight s.1.1≤ S := (weight_fst s.1).trans hc
  have hF : weight s.2≤ S := (weight_snd s).trans hs
  have hb := matrixBound_le s.1.1 hC
  have hfo := fold_weight pre s
  have hout : weight out.2≤8*S^3+4*S^2+3*S+1 :=
    hfo.trans (max_le (by omega) (by omega))
  have hctx : out.1=s.1 := fold_context pre s
  have he : weight out=1+weight out.1+weight out.2 := by
    change weight (out.1,out.2)=_
    exact weight_prod _ _
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change weight out≤20*(S+1)^3
  rw [he,hctx]
  nlinarith

def zeroMatrix (C : NatMatrix) : FlowMatrix :=
  C.map (fun row=>row.map (fun _=>(0,0)))

def zeroMatrixRealizer : Realizer zeroMatrix := map (map (constant (0,0)))

lemma polynomial_zeroMatrix : PolynomialTime zeroMatrixRealizer :=
  polynomial_map (polynomial_map (polynomial_constant (0,0)))

lemma zeroMatrix_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n) :
    zeroMatrix (natCode c)=flowCode (0 : PublishedEdmondsKarp.Flow n) := by
  simp only [zeroMatrix,natCode,flowCode,List.map_ofFn,Function.comp_def]
  rfl

def cube (n : ℕ) : ℕ := n*n*n

def cubeRealizer : Realizer cube :=
  composition (pair (composition (pair identity identity) multiply) identity) multiply

lemma polynomial_cube : PolynomialTime cubeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_identity)
      polynomial_multiply) polynomial_identity) polynomial_multiply

def iterationCount (C : NatMatrix) : ℕ := cube C.length+1

def iterationCountRealizer : Realizer iterationCount :=
  composition (composition listLength cubeRealizer) successor

lemma polynomial_iterationCount : PolynomialTime iterationCountRealizer :=
  polynomial_composition (polynomial_composition polynomial_listLength polynomial_cube)
    polynomial_successor

def steps (C : NatMatrix) : List ℕ := List.range (iterationCount C)

def stepsRealizer : Realizer steps := composition iterationCountRealizer range

lemma polynomial_steps : PolynomialTime stepsRealizer := by
  apply polynomial_boundedRange polynomial_iterationCount (X^3+1)
  intro C
  have h := Nat.pow_le_pow_left (list_length_le_weight C) 3
  simpa only [Function.comp_apply,iterationCount,cube,pow_succ,pow_zero,one_mul,
    eval_add,eval_pow,eval_mul,eval_X,eval_one] using Nat.add_le_add_right h 1

def prepare (z : Context) : List ℕ×State := (steps z.1,(z,zeroMatrix z.1))

def prepareRealizer : Realizer prepare :=
  pair (composition (f := fun z : Context=>z.1) (g := steps) first stepsRealizer)
    (pair identity (composition (f := fun z : Context=>z.1)
      (g := zeroMatrix) first zeroMatrixRealizer))

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair
    (polynomial_composition (f := fun z : Context=>z.1) (g := steps)
      polynomial_first polynomial_steps)
    (polynomial_pair polynomial_identity
      (polynomial_composition (f := fun z : Context=>z.1) (g := zeroMatrix)
        polynomial_first polynomial_zeroMatrix))

def run (z : Context) : FlowMatrix :=
  ((steps z.1).foldl (fun s i=>step (i,s)) (z,zeroMatrix z.1)).2

def runRealizer : Realizer run :=
  composition (composition prepareRealizer (MatchingFPRAS.TreeTyped.fold stepRealizer)) second

theorem polynomial_run : PolynomialTime runRealizer :=
  polynomial_composition (polynomial_composition polynomial_prepare polynomial_loop)
    polynomial_second

lemma step_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (hst : s≠t) (k i : ℕ) :
    step (i,((natCode c,(s.val,t.val)),flowCode (EdmondsKarpAlgorithm.run c s t k)))=
      ((natCode c,(s.val,t.val)),flowCode (EdmondsKarpAlgorithm.run c s t (k+1))) := by
  change ((natCode c,(s.val,t.val)),
    FlowMatrixProgram.advance ((natCode c,flowCode (EdmondsKarpAlgorithm.run c s t k)),
      (s.val,t.val)))=_
  apply congrArg (fun F : FlowMatrix=>((natCode c,(s.val,t.val)),F))
  exact FlowMatrixProgram.advance_code c s t hst _ (EdmondsKarpAlgorithm.run_feasible c s t hst k)

lemma fold_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (hst : s≠t) (steps : List ℕ) (k : ℕ) :
    steps.foldl (fun s i=>step (i,s))
      ((natCode c,(s.val,t.val)),flowCode (EdmondsKarpAlgorithm.run c s t k))=
      ((natCode c,(s.val,t.val)),flowCode (EdmondsKarpAlgorithm.run c s t (k+steps.length))) := by
  induction steps generalizing k with
  | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero]
  | cons i steps ih =>
    rw [List.foldl_cons,step_code c s t hst k i,ih]
    simp only [List.length_cons,Nat.add_comm,Nat.add_left_comm]

theorem run_code {n : ℕ} (c : PublishedEdmondsKarp.Capacity n)
    (s t : Fin n) (hst : s≠t) :
    run (natCode c,(s.val,t.val))=flowCode (EdmondsKarpAlgorithm.maxFlow c s t) := by
  unfold run
  rw [zeroMatrix_code]
  change (List.foldl _ ((natCode c,(s.val,t.val)),
    flowCode (EdmondsKarpAlgorithm.run c s t 0)) (steps (natCode c))).2=_
  rw [fold_code c s t hst]
  simp only [steps,List.length_range,iterationCount,cube,natCode,List.length_ofFn,
    Nat.zero_add,EdmondsKarpAlgorithm.maxFlow,pow_succ,pow_zero,one_mul]

theorem run_maximum (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    {n : ℕ} (c : PublishedEdmondsKarp.Capacity n) (hc : ∀ u,c u u=0)
    (s t : Fin n) (hst : s≠t) :
    ∃ f,run (natCode c,(s.val,t.val))=flowCode f ∧
      PublishedEdmondsKarp.IsMaximum c s t f := by
  exact ⟨EdmondsKarpAlgorithm.maxFlow c s t,run_code c s t hst,
    EdmondsKarpAlgorithm.maxFlow_correct hEK c hc s t hst⟩

end ContingencyTables.FlowLoopProgram

end OAI
