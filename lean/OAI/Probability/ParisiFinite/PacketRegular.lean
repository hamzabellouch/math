import Mathlib
import OAI.Probability.ParisiFinite.LowVector

namespace OAI

/-! Packet Regular. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
namespace PointedTree
open CoherentFock Complex RootSpin
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

 

def PacketRegular (x : X) : (n : ℕ) → (X → Level n) → Prop
  | 0,v => ∀q, AnalyticAt ℝ (fun t => v t q) x
  | n+1,v => ∃ (ι : Type) (_ : Fintype ι) (a : X → ι → Fin 2 → ℂ)
      (d : X → ι → Mode n),
      (∀i q, AnalyticAt ℝ (fun t => a t i q) x) ∧
      (∀i, PacketRegular x n (fun t => (d t i : Level n))) ∧
      (∀t, v t=spinPacket (a t) (d t))

namespace PacketRegular
variable {x : X}

theorem inner : ∀ (n : ℕ) {v w : X → Level n},
    PacketRegular x n v → PacketRegular x n w →
    AnalyticAt ℝ (fun t => ⟪v t,w t⟫_ℂ) x := by
  intro n
  induction n with
  | zero =>
    intro v w hv hw
    change AnalyticAt ℝ (fun t => ∑q : Fin 2, ⟪v t q,w t q⟫_ℂ) x
    apply Finset.analyticAt_fun_sum
    intro q hq
    simp only [RCLike.inner_apply]
    exact (hw q).mul ((Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (hv q))
  | succ n ih =>
    intro v w hv hw
    obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
    obtain ⟨κ,hk,b,e,hb,he,hw⟩ := hw
    let := hi
    let := hk
    simp_rw [hv,hw]
    apply analyticAt_inner_spinPacket a b d e ha hb
    · intro i
      exact ih (hd i) (hd i)
    · intro j
      exact ih (he j) (he j)
    · intro i j
      exact ih (hd i) (he j)

theorem zero (n : ℕ) : PacketRegular x n (fun _ => 0) := by
  cases n with
  | zero => exact fun _ => analyticAt_const
  | succ n =>
    refine ⟨Fin 0,inferInstance,fun _ i => Fin.elim0 i,fun _ i => Fin.elim0 i,?_,?_,?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro t; simp [spinPacket]

theorem add (n : ℕ) {v w : X → Level n}
    (hv : PacketRegular x n v) (hw : PacketRegular x n w) :
    PacketRegular x n (fun t => v t+w t) := by
  cases n with
  | zero => exact fun q => (hv q).add (hw q)
  | succ n =>
    obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
    obtain ⟨κ,hk,b,e,hb,he,hw⟩ := hw
    let := hi
    let := hk
    refine ⟨Sum ι κ,inferInstance,fun t => Sum.elim (a t) (b t),
      fun t => Sum.elim (d t) (e t),?_,?_,?_⟩
    · intro i q; cases i with
      | inl i => exact ha i q
      | inr j => exact hb j q
    · intro i; cases i with
      | inl i => exact hd i
      | inr j => exact he j
    · intro t; dsimp only; rw [hv,hw,spinPacket_sum]

theorem smul (n : ℕ) {v : X → Level n} {z : X → ℂ}
    (hz : AnalyticAt ℝ z x) (hv : PacketRegular x n v) :
    PacketRegular x n (fun t => z t • v t) := by
  cases n with
  | zero => exact fun q => hz.mul (hv q)
  | succ n =>
    obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
    let := hi
    refine ⟨ι,hi,fun t i q => z t*a t i q,d,fun i q => hz.mul (ha i q),hd,?_⟩
    intro t
    dsimp only
    rw [hv,spinPacket_smul]

theorem neg (n : ℕ) {v : X → Level n} (hv : PacketRegular x n v) :
    PacketRegular x n (fun t => -v t) := by
  simpa using smul n (show AnalyticAt ℝ (fun _ : X => (-1:ℂ)) x from analyticAt_const) hv

theorem vac (n : ℕ) : PacketRegular x n (fun _ => PointedTree.vac n) := by
  cases n with
  | zero => exact fun _ => analyticAt_const
  | succ n =>
    refine ⟨Unit,inferInstance,fun _ _ _ => spinCoefficient,fun _ _ => 0,
      fun _ _ => analyticAt_const,fun _ => zero n,?_⟩
    intro t
    ext q
    simp only [spinPacket_apply,Fintype.sum_unique]
    rfl

theorem root (n : ℕ) {v : X → Level n} {A : X → Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀i j, AnalyticAt ℝ (fun t => A t i j) x) (hv : PacketRegular x n v) :
    PacketRegular x n (fun t => PointedTree.root n (A t) (v t)) := by
  cases n with
  | zero =>
    intro q
    change AnalyticAt ℝ (fun t => SpinOperators.act (A t) (v t) q) x
    simp only [SpinOperators.act_apply]
    apply Finset.analyticAt_fun_sum
    intro j hj
    exact (hA q j).mul (hv j)
  | succ n =>
    obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
    let := hi
    refine ⟨ι,hi,fun t i q => ∑j, A t q j * a t i j,d,?_,hd,?_⟩
    · intro i q
      apply Finset.analyticAt_fun_sum
      intro j hj
      exact (hA q j).mul (ha i j)
    · intro t
      change SpinOperators.act (A t) (v t)=_
      rw [hv,act_spinPacket]

end PacketRegular
end PointedTree

namespace PointedTree
open CoherentFock Complex RootSpin
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}
namespace PacketRegular

theorem cost (n : ℕ) {v : X → Level (n+1)} {h : X → Mode n}
    (hh : PacketRegular x n (fun t => (h t : Level n))) (hv : PacketRegular x (n+1) v) :
    PacketRegular x (n+1) (fun t => WZ (h t) (v t)) := by
  classical
  obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
  let := hi
  refine ⟨ι×Fin 2,inferInstance,
    fun t p q => if q=p.2 then phase (if p.2=0 then h t else -h t) (d t p.1)*a t p.1 q else 0,
    fun t p => (if p.2=0 then h t else -h t)+d t p.1,?_,?_,?_⟩
  · intro p q
    by_cases hqp : q=p.2
    · simp only [hqp,ite_true]
      apply AnalyticAt.mul _ (ha p.1 p.2)
      apply analyticAt_phase_of_gram
      have hgram : AnalyticAt ℝ (fun t => ⟪h t,d t p.1⟫_ℂ) x := by
        simpa only [Submodule.coe_inner] using inner n hh (hd p.1)
      by_cases hp : p.2=0
      · simpa only [hp,ite_true] using hgram
      · simpa only [hp,ite_false,inner_neg_left] using hgram.fun_neg
    · simp only [hqp,ite_false]
      exact analyticAt_const
  · intro p
    by_cases hp : p.2=0
    · simpa only [hp,ite_true,Submodule.coe_add] using add n hh (hd p.1)
    · simpa only [hp,ite_false,Submodule.coe_add,Submodule.coe_neg] using add n (neg n hh) (hd p.1)
  · intro t
    dsimp only
    rw [hv,WZ_spinPacket]

end PacketRegular

 
inductive ParamGate (X : Type*)
  | mixer (beta : X → ℝ)
  | cost (gamma : X → ℝ)

def ParamGate.eval (g : ParamGate X) (t : X) : Gate :=
  match g with
  | .mixer f => .mixer (f t)
  | .cost f => .cost (f t)

def ParamGate.regular (g : ParamGate X) (x : X) : Prop :=
  match g with
  | .mixer f => AnalyticAt ℝ f x
  | .cost f => AnalyticAt ℝ f x

def evalWord (w : List (ParamGate X)) (t : X) : List Gate := w.map (fun g => g.eval t)

@[simp] theorem rootEquiv_symm_apply (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ unitary _) (v : Level n) :
    (rootEquiv n A hA).symm v=root n A.conjTranspose v := by
  cases n <;> exact SpinOperators.actEquiv_symm_apply A hA v

theorem analyticAt_R {f : X → ℝ} (hf : AnalyticAt ℝ f x) (i j : Fin 2) :
    AnalyticAt ℝ (fun t => R (f t) i j) x := by
  simp only [R_apply]
  split_ifs with hij
  · exact (Complex.ofRealCLM.analyticAt _).comp (Real.analyticAt_cos.comp hf)
  · exact (show AnalyticAt ℝ (fun _ : X => -I) x from analyticAt_const).mul
      ((Complex.ofRealCLM.analyticAt _).comp (Real.analyticAt_sin.comp hf))

 

theorem ordinary_packetRegular (w : List (ParamGate X))
    (hw : ∀g∈w, g.regular x) : ∀n,
    (∀v : X → Level n, PacketRegular x n v →
      PacketRegular x n (fun t => (ordinary (evalWord w t) n).op (v t))) ∧
    (∀v : X → Level n, PacketRegular x n v →
      PacketRegular x n (fun t => (ordinary (evalWord w t) n).op.symm (v t))) := by
  induction w with
  | nil =>
    intro n
    constructor <;> intro v hv <;> exact hv
  | cons g w ih =>
    have hg : g.regular x := hw g (by simp)
    have hw' : ∀g∈w, g.regular x := fun g hg => hw g (by simp [hg])
    have ih' := ih hw'
    intro n
    cases g with
    | mixer f =>
      change AnalyticAt ℝ f x at hg
      constructor
      · intro v hv
        change PacketRegular x n (fun t => rootEquiv n (R (f t)) _
          ((ordinary (evalWord w t) n).op (v t)))
        simp only [rootEquiv_apply]
        exact PacketRegular.root n (analyticAt_R hg) ((ih' n).1 v hv)
      · intro v hv
        change PacketRegular x n (fun t => (ordinary (evalWord w t) n).op.symm
          ((rootEquiv n (R (f t)) _).symm (v t)))
        simp only [rootEquiv_symm_apply,R_star]
        exact (ih' n).2 _ (PacketRegular.root n (analyticAt_R hg.neg) hv)
    | cost f =>
      change AnalyticAt ℝ f x at hg
      cases n with
      | zero => exact ih' 0
      | succ n =>
        have hins : PacketRegular x n
            (fun t => ((ordinary (evalWord w t) n).insertion : Level n)) :=
          (ih' n).2 _ (PacketRegular.root n (fun _ _ => analyticAt_const)
            ((ih' n).1 _ (PacketRegular.vac n)))
        have hd : PacketRegular x n (fun t => (-(f t:ℂ)) •
            ((ordinary (evalWord w t) n).insertion : Level n)) :=
          PacketRegular.smul n ((Complex.ofRealCLM.analyticAt _).comp hg).neg hins
        constructor
        · intro v hv
          change PacketRegular x (n+1) (fun t => WZ
            ((-(f t:ℂ)) • (ordinary (evalWord w t) n).insertion)
            ((ordinary (evalWord w t) (n+1)).op (v t)))
          exact PacketRegular.cost n hd ((ih' (n+1)).1 v hv)
        · intro v hv
          change PacketRegular x (n+1) (fun t => (ordinary (evalWord w t) (n+1)).op.symm
            (WZ (-((-(f t:ℂ)) • (ordinary (evalWord w t) n).insertion)) (v t)))
          exact (ih' (n+1)).2 _ (PacketRegular.cost n (PacketRegular.neg n hd) hv)

 

theorem ordinary_insertion_packetRegular (w : List (ParamGate X))
    (hw : ∀g∈w, g.regular x) (n : ℕ) :
    PacketRegular x n (fun t => ((ordinary (evalWord w t) n).insertion : Level n)) := by
  have h := ordinary_packetRegular w hw n
  exact h.2 _ (PacketRegular.root n (fun _ _ => analyticAt_const)
    (h.1 _ (PacketRegular.vac n)))

end PointedTree

namespace CoherentFock
open Complex PointedTree
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] {x : X}

 

theorem analyticAt_inner_spinPacket_creation {ι : Type*} [Fintype ι]
    (a : X → ι → Fin 2 → ℂ) (d : X → ι → E) (h : X → E)
    (ha : ∀i q, AnalyticAt ℝ (fun t => a t i q) x)
    (hd : ∀i, AnalyticAt ℝ (fun t => ⟪d t i,d t i⟫_ℂ) x)
    (hdh : ∀i, AnalyticAt ℝ (fun t => ⟪d t i,h t⟫_ℂ) x) :
    AnalyticAt ℝ (fun t => ⟪spinPacket (a t) (d t),plusEmbedding (creationVacuum (h t))⟫_ℂ) x := by
  simp_rw [inner_spinPacket_creation]
  apply Finset.analyticAt_fun_sum
  intro i hi
  have h0 : AnalyticAt ℝ (fun t => conj (a t i 0)) x :=
    (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (ha i 0)
  have h1 : AnalyticAt ℝ (fun t => conj (a t i 1)) x :=
    (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (ha i 1)
  have hn : AnalyticAt ℝ (fun t => (Real.exp (-‖d t i‖^2/2):ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp (analyticAt_rexp.comp
      (analyticAt_norm_sq_of_inner (fun t => d t i) (hd i)).neg.div_const)
  exact (((show AnalyticAt ℝ (fun _ : X => -I) x from analyticAt_const).mul (h0.add h1)).mul
    (show AnalyticAt ℝ (fun _ : X => spinCoefficient) x from analyticAt_const)).mul hn |>.mul (hdh i)

end CoherentFock

namespace PointedTree
open CoherentFock Complex
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X}

namespace PacketRegular

theorem inner_creation (n : ℕ) {v : X → Level (n+1)} {h : X → Mode n}
    (hv : PacketRegular x (n+1) v) (hh : PacketRegular x n (fun t => (h t : Level n))) :
    AnalyticAt ℝ (fun t => ⟪v t,plusEmbedding (creationVacuum (h t))⟫_ℂ) x := by
  obtain ⟨ι,hi,a,d,ha,hd,hv⟩ := hv
  let := hi
  simp_rw [hv]
  exact analyticAt_inner_spinPacket_creation a d h ha
    (fun i => inner n (hd i) (hd i)) (fun i => inner n (hd i) hh)

end PacketRegular

 

theorem analyticAt_ordinary_insertion_gram (w u : List (ParamGate X))
    (hw : ∀g∈w, g.regular x) (hu : ∀g∈u, g.regular x) (n : ℕ) :
    AnalyticAt ℝ (fun t => ⟪(ordinary (evalWord w t) n).insertion,
      (ordinary (evalWord u t) n).insertion⟫_ℂ) x :=
  PacketRegular.inner n (ordinary_insertion_packetRegular w hw n)
    (ordinary_insertion_packetRegular u hu n)

 

theorem analyticAt_ordinaryValue (w : List (ParamGate X))
    (hw : ∀g∈w, g.regular x) : AnalyticAt ℝ (fun t => ordinaryValue (evalWord w t)) x := by
  let n := w.length
  have hl (t : X) : (evalWord w t).length=n := by simp [evalWord,n]
  have h := PacketRegular.inner_creation n
    (ordinary_insertion_packetRegular w hw (n+1)) (ordinary_insertion_packetRegular w hw n)
  have hr := (Complex.reCLM.analyticAt _).comp h
  convert hr using 1
  ext t
  dsimp only [Function.comp_def,Complex.reCLM_apply]
  rw [ordinaryValue,hl,treeEnergy,ordinary_insertion_empty _ n (by rw [hl])]
  rfl

end PointedTree

 

open Filter Set Topology
namespace AnalyticVisibility
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 
theorem dense_nonzero (f : E → ℝ) (hf : AnalyticOnNhd ℝ f Set.univ)
    (x₀ : E) (h₀ : f x₀ ≠ 0) : Dense {x | f x ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  by_contra h
  have hz : ∀x ∈ U, f x=0 := by
    intro x hx
    by_contra hx'
    apply h
    exact ⟨x,hx,hx'⟩
  obtain ⟨x,hx⟩ := hne
  have he : f =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hz y hy
  have hident := hf.eq_of_eventuallyEq analyticOnNhd_const he
  exact h₀ (congrFun hident x₀)

 

theorem dense_all_nonzero {ι : Type*} [Finite ι] (f : ι → E → ℝ)
    (hf : ∀i, AnalyticOnNhd ℝ (f i) Set.univ)
    (hn : ∀i, ∃x, f i x ≠ 0) : Dense {x | ∀i, f i x ≠ 0} := by
  have ho (i : ι) : IsOpen {x | f i x ≠ 0} :=
    isOpen_ne_fun ((hf i).continuous) continuous_const
  have hd (i : ι) : Dense {x | f i x ≠ 0} := by
    obtain ⟨x,hx⟩ := hn i
    exact dense_nonzero (f i) (hf i) x hx
  classical
  let := Fintype.ofFinite ι
  have hs (s : Finset ι) : Dense {x | ∀i ∈ s, f i x ≠ 0} := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      convert (hd i).inter_of_isOpen_left ih (ho i) using 1
      ext x
      simp only [Finset.mem_insert,forall_eq_or_imp,Set.mem_ofPred_eq,Set.mem_inter_iff]
  simpa using hs Finset.univ

 

theorem exists_perturbation {ι : Type*} [Finite ι] (f : ι → E → ℝ)
    (hf : ∀i, AnalyticOnNhd ℝ (f i) Set.univ)
    (hn : ∀i, ∃x, f i x ≠ 0) (energy : E → ℝ) (x : E)
    (henergy : ContinuousAt energy x) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃y, dist y x < δ ∧ |energy y-energy x| < ε ∧ ∀i, f i y ≠ 0 := by
  have he : ∀ᶠ y in 𝓝 x, |energy y-energy x| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp henergy.tendsto ε hε)
  have hb : ∀ᶠ y in 𝓝 x, dist y x < δ := Metric.ball_mem_nhds x hδ
  obtain ⟨y,hy,hv⟩ := (dense_all_nonzero f hf hn).inter_nhds_nonempty (he.and hb)
  exact ⟨y,hv.2,hv.1,hy⟩

end AnalyticVisibility

 

open scoped InnerProductSpace ComplexConjugate Topology
namespace HilbertChain
variable (H : ℕ → Type*) [∀n, NormedAddCommGroup (H n)] [∀n, InnerProductSpace ℂ (H n)]
variable (step : ∀n, H n →ₗᵢ[ℂ] H (n+1))

def up (n m : ℕ) (h : n ≤ m) : H n →ₗᵢ[ℂ] H m :=
  Nat.leRecOn h (fun {k} T => (step k).comp T) LinearIsometry.id

@[simp] theorem up_self (n : ℕ) : up H step n n le_rfl=LinearIsometry.id := by
  exact Nat.leRecOn_self _

@[simp] theorem up_succ (n m : ℕ) (h : n ≤ m) :
    up H step n (m+1) (h.trans (Nat.le_succ m))=(step m).comp (up H step n m h) := by
  exact Nat.leRecOn_succ h _

@[simp] theorem up_comp (n m k : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    (up H step m k hmk).comp (up H step n m hnm)=up H step n k (hnm.trans hmk) := by
  induction k, hmk using Nat.le_induction with
  | base => simp
  | succ k h ih => rw [up_succ H step m k h,up_succ H step n k (hnm.trans h)];
                   simpa only [LinearIsometry.comp_assoc] using congrArg ((step k).comp) ih

instance : DirectedSystem H (fun {n m} h => up H step n m h) where
  map_self x := by simp
  map_map := by
    intro k j i hij hjk x
    exact congrArg (fun T => T x) (up_comp H step i j k hij hjk)

abbrev Algebraic := DirectLimit H (up H step)

def incl (n : ℕ) : H n →ₗ[ℂ] Algebraic H step :=
  DirectLimit.Module.of ℂ ℕ H (up H step) n

@[simp] theorem incl_up (n m : ℕ) (h : n ≤ m) (x : H n) :
    incl H step m (up H step n m h x)=incl H step n x := DirectLimit.Module.of_f

def inner (x y : Algebraic H step) : ℂ :=
  DirectLimit.lift₂ (up H step) (up H step) (fun _ x y => ⟪x,y⟫_ℂ)
    (fun n m h x y => (up H step n m h).inner_map_map x y |>.symm) x y

@[simp] theorem inner_incl (n : ℕ) (x y : H n) :
    inner H step (incl H step n x) (incl H step n y)=⟪x,y⟫_ℂ :=
  DirectLimit.lift₂_def _ _ _ _ n x y

@[elab_as_elim] theorem induction {P : Algebraic H step → Prop}
    (h : ∀n x, P (incl H step n x)) (x) : P x := DirectLimit.induction _ h x

@[elab_as_elim] theorem induction₂ {P : Algebraic H step → Algebraic H step → Prop}
    (h : ∀n x y, P (incl H step n x) (incl H step n y)) (x y) : P x y :=
  DirectLimit.induction₂ _ h x y

@[elab_as_elim] theorem induction₃
    {P : Algebraic H step → Algebraic H step → Algebraic H step → Prop}
    (h : ∀n x y z, P (incl H step n x) (incl H step n y) (incl H step n z)) (x y z) : P x y z :=
  DirectLimit.induction₃ _ h x y z

@[instance_reducible] def core : InnerProductSpace.Core ℂ (Algebraic H step) where
  inner := inner H step
  conj_inner_symm := induction₂ H step (fun n x y => by simp [inner_conj_symm])
  re_inner_nonneg := induction H step (fun n x => by rw [inner_incl]; exact inner_self_nonneg)
  add_left := induction₃ H step (fun n x y z => by rw [←map_add,inner_incl,inner_incl,inner_incl,inner_add_left])
  smul_left x y r := induction₂ H step (fun n x y => by rw [←map_smul,inner_incl,inner_incl,inner_smul_left]) x y
  definite := induction H step (fun n x hx => by
    rw [inner_incl,inner_self_eq_zero] at hx
    rw [hx,map_zero])

instance : NormedAddCommGroup (Algebraic H step) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := core H step)
instance : InnerProductSpace ℂ (Algebraic H step) :=
  InnerProductSpace.ofCore (core H step).toCore

@[simp] theorem inner_incl' (n : ℕ) (x y : H n) :
    ⟪incl H step n x,incl H step n y⟫_ℂ=⟪x,y⟫_ℂ := inner_incl H step n x y

def inclusion (n : ℕ) : H n →ₗᵢ[ℂ] Algebraic H step :=
  LinearMap.isometryOfInner (incl H step n) (inner_incl' H step n)

abbrev Space := UniformSpace.Completion (Algebraic H step)

def embed (n : ℕ) : H n →ₗᵢ[ℂ] Space H step :=
  (UniformSpace.Completion.toComplₗᵢ : Algebraic H step →ₗᵢ[ℂ] Space H step).comp (inclusion H step n)

@[simp] theorem embed_up (n m : ℕ) (h : n ≤ m) (x : H n) :
    embed H step m (up H step n m h x)=embed H step n x := by
  change ((incl H step m (up H step n m h x) : Algebraic H step) : Space H step)=_
  rw [incl_up]
  rfl

@[simp] theorem embed_step (n : ℕ) (x : H n) :
    embed H step (n+1) (step n x)=embed H step n x := by
  simpa using embed_up H step n (n+1) (Nat.le_succ n) x

end HilbertChain

namespace HilbertChain
variable (H : ℕ → Type*) [∀n, NormedAddCommGroup (H n)] [∀n, InnerProductSpace ℂ (H n)]
variable (step : ∀n, H n →ₗᵢ[ℂ] H (n+1))

 

theorem denseRange_embed : DenseRange (fun x : Σn, H n => embed H step x.1 x.2) := by
  have hr : Set.range (fun x : Σn, H n => embed H step x.1 x.2)=
      Set.range (fun x : Algebraic H step => (x : Space H step)) := by
    ext v
    constructor
    · rintro ⟨⟨n,x⟩,rfl⟩
      exact ⟨incl H step n x,rfl⟩
    · rintro ⟨x,rfl⟩
      induction x using HilbertChain.induction H step with
      | h n x => exact ⟨⟨n,x⟩,rfl⟩
  change Dense _
  rw [hr]
  exact UniformSpace.Completion.denseRange_coe

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (g : ∀n, H n →ₗᵢ[ℂ] F)
variable (hg : ∀n x, g (n+1) (step n x)=g n x)

include hg in
theorem lift_compat (n m : ℕ) (h : n ≤ m) (x : H n) :
    g m (up H step n m h x)=g n x := by
  induction m,h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    rw [up_succ H step n m h]
    change g (m+1) (step m (up H step n m h x)) = _
    rw [hg,ih]

def liftAlgebraic : Algebraic H step →ₗᵢ[ℂ] F where
  toLinearMap := DirectLimit.Module.lift ℂ ℕ H (up H step) (fun n => (g n).toLinearMap)
    (lift_compat H step g hg)
  norm_map' x := by
    induction x using HilbertChain.induction H step with
    | h n x =>
      change ‖g n x‖=‖incl H step n x‖
      rw [(g n).norm_map]
      exact ((inclusion H step n).norm_map x).symm

@[simp] theorem liftAlgebraic_incl (n : ℕ) (x : H n) :
    liftAlgebraic H step g hg (incl H step n x)=g n x := rfl

end HilbertChain

namespace HilbertChain
variable (H : ℕ → Type*) [∀n, NormedAddCommGroup (H n)] [∀n, InnerProductSpace ℂ (H n)]
variable (step : ∀n, H n →ₗᵢ[ℂ] H (n+1))
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (g : ∀n, H n →ₗᵢ[ℂ] F)
variable (hg : ∀n x, g (n+1) (step n x)=g n x)

 
def lift : Space H step →ₗᵢ[ℂ] F where
  toLinearMap := (liftAlgebraic H step g hg).toContinuousLinearMap.fromCompletion.toLinearMap
  norm_map' x := by
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq ((liftAlgebraic H step g hg).toContinuousLinearMap.fromCompletion.continuous.norm)
        continuous_norm) fun y => ?_
    change ‖(liftAlgebraic H step g hg).toContinuousLinearMap.fromCompletion
      (y : Space H step)‖ = ‖(y : Space H step)‖
    rw [ContinuousLinearMap.fromCompletion_apply_coe,UniformSpace.Completion.norm_coe]
    exact (liftAlgebraic H step g hg).norm_map y

@[simp] theorem lift_embed (n : ℕ) (x : H n) :
    lift H step g hg (embed H step n x)=g n x := by
  change (liftAlgebraic H step g hg).toContinuousLinearMap.fromCompletion
    (incl H step n x : Algebraic H step)=g n x
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

omit [CompleteSpace F] in
 

theorem ext {A B : Space H step →L[ℂ] F} (h : ∀n x, A (embed H step n x)=B (embed H step n x)) :
    A=B := by
  apply ContinuousLinearMap.ext
  intro x
  exact congrFun ((denseRange_embed H step).equalizer A.continuous B.continuous
    (by funext z; exact h z.1 z.2)) x

end HilbertChain

 
namespace PointedTree

abbrev ModeSpace (n : ℕ) : Type := ↥(Mode n)

abbrev wholeStep (n : ℕ) : Level n →ₗᵢ[ℂ] Level (n+1) := (empty n).toLinearIsometry
abbrev modeStep (n : ℕ) : Mode n →ₗᵢ[ℂ] Mode (n+1) := centeredMap (empty n)
abbrev WholeInfinity := HilbertChain.Space Level wholeStep
abbrev ModeInfinity := HilbertChain.Space ModeSpace modeStep
abbrev wholeEmbed (n : ℕ) : Level n →ₗᵢ[ℂ] WholeInfinity := HilbertChain.embed Level wholeStep n
abbrev modeEmbed (n : ℕ) : Mode n →ₗᵢ[ℂ] ModeInfinity := HilbertChain.embed ModeSpace modeStep n

def vacuumInfinity : WholeInfinity := wholeEmbed 0 (vac 0)

@[simp] theorem embed_vac (n : ℕ) : wholeEmbed n (vac n)=vacuumInfinity := by
  induction n with
  | zero => rfl
  | succ n ih => rw [←empty_vac n]; exact (HilbertChain.embed_step Level wholeStep n _).trans ih

@[simp] theorem norm_vacuumInfinity : ‖vacuumInfinity‖=1 := by
  rw [vacuumInfinity,(wholeEmbed 0).norm_map,norm_vac]

 
def modeInWhole : ModeInfinity →ₗᵢ[ℂ] WholeInfinity :=
  HilbertChain.lift ModeSpace modeStep
    (fun n => (wholeEmbed n).comp (Submodule.subtypeₗᵢ (Mode n))) (by
      intro n x
      change wholeEmbed (n+1) ((empty n).toLinearIsometry x)=wholeEmbed n x
      exact HilbertChain.embed_step Level wholeStep n x)

@[simp] theorem modeInWhole_embed (n : ℕ) (d : Mode n) :
    modeInWhole (modeEmbed n d)=wholeEmbed n (d : Level n) :=
  HilbertChain.lift_embed ModeSpace modeStep _ _ n d

 
theorem modeInWhole_centered (x : ModeInfinity) : ⟪vacuumInfinity,modeInWhole x⟫_ℂ=0 := by
  have h : ∀n (d : Mode n), ⟪vacuumInfinity,modeInWhole (modeEmbed n d)⟫_ℂ=0 := by
    intro n d
    rw [modeInWhole_embed,←embed_vac n,(wholeEmbed n).inner_map_map]
    exact (mem_centered _ _).mp d.property
  exact congrFun ((HilbertChain.denseRange_embed ModeSpace modeStep).equalizer
    (continuous_const.inner modeInWhole.continuous : Continuous fun x => ⟪vacuumInfinity,modeInWhole x⟫_ℂ)
    continuous_const (by funext z; exact h z.1 z.2)) x

 

def shiftInfinity : ModeInfinity →ₗᵢ[ℂ] ModeInfinity :=
  HilbertChain.lift ModeSpace modeStep (fun n => (modeEmbed (n+1)).comp (rootShift n)) (by
    intro n d
    change modeEmbed (n+2) (rootShift (n+1) (centeredMap (empty n) d))=
      modeEmbed (n+1) (rootShift n d)
    rw [←rootShift_empty]
    exact HilbertChain.embed_step ModeSpace modeStep (n+1) _)

@[simp] theorem shiftInfinity_embed (n : ℕ) (d : Mode n) :
    shiftInfinity (modeEmbed n d)=modeEmbed (n+1) (rootShift n d) :=
  HilbertChain.lift_embed ModeSpace modeStep _ _ n d

 
def energyInfinity (d : ModeInfinity) : ℝ := (⟪d,shiftInfinity d⟫_ℂ).re

@[simp] theorem energyInfinity_embed (n : ℕ) (d : Mode n) :
    energyInfinity (modeEmbed n d)=treeEnergy n d := by
  rw [energyInfinity,shiftInfinity_embed]
  have he := HilbertChain.embed_step ModeSpace modeStep n d
  change modeEmbed (n+1) (centeredMap (empty n) d)=modeEmbed n d at he
  rw [←he,(modeEmbed (n+1)).inner_map_map]
  rfl

theorem continuous_energyInfinity : Continuous energyInfinity :=
  Complex.continuous_re.comp (continuous_id.inner shiftInfinity.continuous :
    Continuous fun d => ⟪d,shiftInfinity d⟫_ℂ)

theorem energyInfinity_sub_le (d e : ModeInfinity) :
    |energyInfinity d-energyInfinity e| ≤ (‖d‖+‖e‖)*‖d-e‖ := by
  have he : ⟪d,shiftInfinity d⟫_ℂ-⟪e,shiftInfinity e⟫_ℂ=
      ⟪d-e,shiftInfinity d⟫_ℂ+⟪e,shiftInfinity (d-e)⟫_ℂ := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    ring
  change |(⟪d,shiftInfinity d⟫_ℂ).re-(⟪e,shiftInfinity e⟫_ℂ).re| ≤ _
  rw [←Complex.sub_re,he,Complex.add_re]
  calc
    _ ≤ |(⟪d-e,shiftInfinity d⟫_ℂ).re|+|(⟪e,shiftInfinity (d-e)⟫_ℂ).re| := abs_add_le _ _
    _ ≤ ‖d-e‖*‖shiftInfinity d‖+‖e‖*‖shiftInfinity (d-e)‖ :=
      add_le_add ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
        ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
    _ = _ := by rw [shiftInfinity.norm_map,shiftInfinity.norm_map]; ring

 

def insertionInfinity (w : List Gate) : ModeInfinity :=
  modeEmbed w.length (ordinary w w.length).insertion

theorem insertionInfinity_stable (w : List Gate) (n : ℕ) (hn : w.length ≤ n) :
    modeEmbed n (ordinary w n).insertion=insertionInfinity w := by
  induction n,hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [←ordinary_insertion_empty w n hn]
    exact (HilbertChain.embed_step ModeSpace modeStep n _).trans ih

@[simp] theorem norm_insertionInfinity (w : List Gate) : ‖insertionInfinity w‖=1 := by
  rw [insertionInfinity,(modeEmbed _).norm_map,EvenUnitary.norm_insertion]

@[simp] theorem energy_insertionInfinity (w : List Gate) :
    energyInfinity (insertionInfinity w)=ordinaryValue w := energyInfinity_embed _ _

end PointedTree

end

end OAI
