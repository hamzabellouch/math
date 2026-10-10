import OAI.Computability.MeanPayoff.Preparation

namespace OAI

namespace MeanPayoff.TreeDevice.Certified.DetPost
open BinaryData Code
noncomputable def boolean : Device Compare.bitTree boolData (fun b : Bool => b) :=
  (TreeDevice.branch (TreeDevice.identity Compare.bitTree)
    (TreeDevice.constant Compare.bitTree boolData true)
    (TreeDevice.constant Compare.bitTree boolData false)).extFun (by intro b; cases b <;> rfl)
 theorem boolean_poly : PolynomialCost boolean :=
  PolynomialCost.branch (LinearCost.identity _).polynomial (LinearCost.constant _ _ _).polynomial
    (LinearCost.constant _ _ _).polynomial
noncomputable def digits : Code (List Bool) Digits := by
  let D := Map.device boolean
  refine ⟨Digits.mk,D.recode encode encode _root_.id Digits.mk (fun _ => rfl) (fun _ => ?_),?_⟩
  · simp [encode]
  · obtain ⟨K,d,h⟩ := PolynomialCost.map boolean_poly
    exact ⟨K,d,fun z => h z⟩
 theorem digits_eval (bs : List Bool) : digits bs=⟨bs⟩ := rfl
end MeanPayoff.TreeDevice.Certified.DetPost

section
namespace MeanPayoff.Box5
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (config_ext)
def place (i : Fin 3) : Fin 5 := ⟨i.val,by omega⟩
 theorem injective : Function.Injective place := by intro i j h; exact Fin.ext (congrArg (fun x : Fin 5 => x.val) h)
 theorem installs (a b c : List Bool) :
    install place (core [] [] []) ![a,b,c]=core a b c := by
  funext i; fin_cases i
  · exact install_at place injective _ _ 0
  · exact install_at place injective _ _ 1
  · exact install_at place injective _ _ 2
  · exact install_off place _ _ _ (by intro j; fin_cases j <;> decide)
  · exact install_off place _ _ _ (by intro j; fin_cases j <;> decide)
noncomputable def program : Program 5 := rename Box.program place
 theorem quiet : CoinFree program := by intro q top b; rfl
 theorem runs (bs out : List Bool) (bits : ℕ→Bool) :
    advance program bits ⟨some program.start,core bs [] [],out⟩
      (2*bs.length+2+feedCost bs+1)=⟨none,core [] (encode (listData bs)) [],out⟩ := by
  have h := rename_advance Box.program place injective (core [] [] [])
    (Box.cfg .reverse bs [] [] out) bits (2*bs.length+2+feedCost bs+1)
  rw [Box.boxes] at h
  change advance (rename Box.program place) bits
    ⟨some (Box.enc .reverse),core bs [] [],out⟩ _=_
  simp only [renamed,Box.cfg,Box.stopped,installs,List.append_nil] at h
  convert h using 1; rfl
end MeanPayoff.Box5

end

section
namespace MeanPayoff.Emit
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (advance_add config_ext)
def program : RegisterBits.Program 5 where
  states := 5
  start := 0
  read _ := 0
  transition q top _ := match q.val with
    | 0 => top.map (fun b => ⟨if b then 1 else 4,.pop,none⟩)
    | 1 => top.map (fun b => if b then ⟨2,.pop,none⟩ else ⟨0,.pop,some false⟩)
    | 2 => some ⟨3,.pop,none⟩
    | 3 => some ⟨0,.pop,some true⟩
    | _ => none
def cfg (q : Fin 5) (xs out : List Bool) : Config program := ⟨some q,core xs [] [],out⟩
def cost (bs : List Bool) : ℕ := (bs.map (fun b => if b then 4 else 2)).sum+2
 theorem quiet : CoinFree program := by intro q top b; rfl
 theorem nil_run (xs out : List Bool) (bits : ℕ→Bool) :
    advance program bits (cfg 0 (false::xs) out) 2=⟨none,core xs [] [],out⟩ := by
  apply config_ext <;> (try rfl)
  · funext i; fin_cases i <;> rfl
  · change out++[]=out
    exact List.append_nil out
 theorem one (b : Bool) (xs out : List Bool) (bits : ℕ→Bool) :
    advance program bits (cfg 0 (consCode b++xs) out) (if b then 4 else 2)=cfg 0 xs (out++[b]) := by
  cases b <;> apply config_ext <;> (try rfl)
  all_goals first
  | (funext i; fin_cases i <;> rfl)
  | simp [advance,RegisterBits.step,cfg,program,core,consCode,BinaryStack.applyOp]
 theorem runs (bs xs out : List Bool) (bits : ℕ→Bool) :
    advance program bits (cfg 0 (encode (listData bs)++xs) out) (cost bs)=
      ⟨none,core xs [] [],out++bs⟩ := by
  induction bs generalizing out bits with
  | nil => simpa only [cost,List.map_nil,List.sum_nil,Nat.zero_add,List.append_nil,encode_list_nil,List.singleton_append] using nil_run xs out bits
  | cons b bs ih =>
    have hc : cost (b::bs)=(if b then 4 else 2)+cost bs := by simp only [cost,List.map_cons,List.sum_cons]; omega
    rw [hc,encode_list_cons,List.append_assoc,advance_add,one,ih]
    simp only [List.append_assoc,List.singleton_append]
 theorem bound (bs : List Bool) : cost bs≤4*bs.length+2 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hc : cost (b::bs)=(if b then 4 else 2)+cost bs := by simp only [cost,List.map_cons,List.sum_cons]; omega
    rw [hc,List.length_cons]
    split <;> omega
end MeanPayoff.Emit

end

section
namespace MeanPayoff.RegisterBits.Sequence5
open BinaryData.Take (advance_add)
variable (P Q : Program 5)
def flow : Flow.Program 5 where
  nodes := 2
  start := 0
  block := ![P,Q]
  read _ := 0
  next p _ _ := if p=0 then some ⟨1,.keep,none⟩ else none
noncomputable def program : Program 5 := Flow.compile (flow P Q)
 theorem quiet (hP : CoinFree P) (hQ : CoinFree Q) : CoinFree (program P Q) :=
  Flow.compile_coinFree _ (by intro p; fin_cases p; exact hP; exact hQ) (by intros; rfl)
 theorem finish_output (F : Flow.Program 5) (p : Fin F.nodes)
    (s t : Fin 5→List Bool) (out result : List Bool) (bits : ℕ→Bool) (N : ℕ)
    (h : advance (F.block p) bits ⟨some (F.block p).start,s,out⟩ N=⟨none,t,result⟩)
    (hn : ∀ top b, F.next p top b=none) :
    ∃ n≤N+1, advance (Flow.compile F) bits (Flow.state F p s out) n=⟨none,t,result⟩ := by
  obtain ⟨n,hn',hh⟩ := Flow.macro_runs F p s out bits N (by rw [h])
  rw [h] at hh
  refine ⟨n+1,by omega,?_⟩
  simp only [advance,hh,Flow.step_boundary,hn]
 theorem runs (s t u : Fin 5→List Bool) (out result : List Bool) (N M : ℕ)
    (hP : ∀ bits, advance P bits ⟨some P.start,s,out⟩ N=⟨none,t,out⟩)
    (hQ : ∀ bits, advance Q bits ⟨some Q.start,t,out⟩ M=⟨none,u,result⟩)
    (bits : ℕ→Bool) : advance (program P Q) bits ⟨some (program P Q).start,s,out⟩ (N+M+2)=⟨none,u,result⟩ := by
  obtain ⟨a,ha,ea⟩ := Flow.hop (flow P Q) (0 : Fin 2) (1 : Fin 2) s t out bits N (hP bits) (by intros; rfl)
  obtain ⟨b,hb,eb⟩ := finish_output (flow P Q) (1 : Fin 2) t u out result (fun j => bits (a+j)) M (hQ _) (by intros; rfl)
  apply advance_pad _ _ _ bits (n:=a+b) (by omega) ?_ rfl
  change advance _ bits (Flow.state (flow P Q) (0 : Fin 2) s out) (a+b)=_
  rw [advance_add,ea,eb]
  rfl
end MeanPayoff.RegisterBits.Sequence5

end

namespace MeanPayoff.DetRealizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
noncomputable def preTail : Program 5 := Sequence5.program (moveCode 1 0) DetPreparation.device.program
noncomputable def pre : Program 5 := Sequence5.program Box5.program preTail
noncomputable def preCost (d : Digits) : ℕ :=
  (2*d.bits.length+2+feedCost d.bits+1)+(6*treeSize (encode d)+3+DetPreparation.device.limit d+2)+2
 theorem pre_quiet : CoinFree pre :=
  Sequence5.quiet _ _ Box5.quiet (Sequence5.quiet _ _ (by intro q top b; rfl) DetPreparation.device.quiet)
 theorem pre_runs (d : Digits) (bits : ℕ→Bool) :
    advance pre bits ⟨some pre.start,core d.bits [] [],[]⟩ (preCost d)=
      ⟨none,store (encode (DetPreparation.value d)) [],[]⟩ := by
  have hd : (encode d : Data)=listData d.bits := Halve.listTree_boolData _
  apply Sequence5.runs Box5.program preTail (core d.bits [] []) (core [] (BinaryData.encode (encode d)) [])
    (store (encode (DetPreparation.value d)) []) [] [] _ _ ?_ ?_ bits
  · intro cs; rw [hd]; exact Box5.runs d.bits [] cs
  · intro cs
    apply Sequence5.runs (moveCode 1 0) DetPreparation.device.program _ (store (encode d) []) _ [] [] _ _ ?_ ?_ cs
    · intro ds
      convert move10 (encode d) [] [] [] [] ds using 1 <;> simp only [store,core,List.append_nil]
    · exact DetPreparation.device.correct d [] []
noncomputable def post : Program 5 := Sequence5.program DetPost.digits.device.program Emit.program
noncomputable def postCost (z : List Bool) : ℕ := DetPost.digits.device.limit z+Emit.cost z+2
 theorem post_quiet : CoinFree post := Sequence5.quiet _ _ DetPost.digits.device.quiet Emit.quiet
 theorem post_runs (z : List Bool) (bits : ℕ→Bool) :
    advance post bits ⟨some post.start,store (encode z) [],[]⟩ (postCost z)=
      ⟨none,core [] [] [],z⟩ := by
  apply Sequence5.runs DetPost.digits.device.program Emit.program _ (store (encode (DetPost.digits z)) []) _ [] _ _ _
    (DetPost.digits.device.correct z [] []) ?_ bits
  intro cs
  have hd : (encode (DetPost.digits z) : Data)=listData z := Halve.listTree_boolData _
  convert Emit.runs z [] [] cs using 1 <;> simp only [List.nil_append,hd] ; rfl
 theorem digits_length (d : Digits) : d.bits.length≤treeSize (encode d) := by
  have h := list_length_le_size boolData d.bits
  change d.bits.length≤treeSize (listTree boolData d.bits)
  omega
 theorem post_polynomial : ∃ K e, ∀ z, postCost z≤K*(treeSize (encode z)+1)^e := by
  have hi := PolyBound.base (fun z : List Bool => treeSize (encode z))
  have hc := polynomial_limit DetPost.digits.polynomial _ (fun z : List Bool => z) hi
  have he := ((PolyBound.const _ 4).mul hi).add (PolyBound.const _ 2)
  have hb : PolyBound (fun z : List Bool => treeSize (encode z)) (fun z => Emit.cost z) :=
    he.mono (fun z => (Emit.bound _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Size.length z)) 2))
  exact (hc.add hb).add (PolyBound.const _ 2)
noncomputable def program : Program 5 := Sequence5.program pre post
noncomputable def limit (d : Digits) : ℕ := preCost d+postCost (DetPreparation.value d)+2
 theorem program_quiet : CoinFree program := Sequence5.quiet _ _ pre_quiet post_quiet
 theorem runs (d : Digits) (bits : ℕ→Bool) :
    advance program bits (RegisterBits.initial program d.bits) (limit d)=
      ⟨none,core [] [] [],DetPreparation.value d⟩ := by
  have hi : RegisterBits.initial program d.bits=⟨some program.start,core d.bits [] [],[]⟩ := by
    apply BinaryData.Take.config_ext <;> (try rfl)
    funext i; fin_cases i <;> rfl
  rw [hi]
  exact Sequence5.runs pre post _ _ _ [] _ _ _ (pre_runs d) (post_runs _) bits
 theorem pre_bound : PolyBound DetPreparation.resource preCost := by
  have hl := DetPreparation.input_bound.mono digits_length
  have hf := ((PolyBound.const _ 5).mul hl).mono (fun d => feedCost_le d.bits)
  exact (((((PolyBound.const _ 2).mul hl).add (PolyBound.const _ 2)).add hf).add (PolyBound.const _ 1)).add
    (((((PolyBound.const _ 6).mul DetPreparation.input_bound).add (PolyBound.const _ 3)).add DetPreparation.cost_bound).add
      (PolyBound.const _ 2)) |>.add (PolyBound.const _ 2)
 theorem post_bound : PolyBound DetPreparation.resource (fun d => postCost (DetPreparation.value d)) := by
  obtain ⟨K,e,h⟩ := post_polynomial
  exact ((PolyBound.const _ K).mul ((DetPreparation.output_bound.add (PolyBound.const _ 1)).pow e)).mono
    (fun d => h (DetPreparation.value d))
 theorem limit_bound : PolyBound DetPreparation.resource limit := (pre_bound.add post_bound).add (PolyBound.const _ 2)
end MeanPayoff.DetRealizer

namespace MeanPayoff.DetRealizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
 theorem list_size (bs : List Bool) : treeSize (listData bs)≤4*bs.length+1 := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    change (encode (listData (b::bs))).length≤_
    rw [encode_list_cons,List.length_append,List.length_cons]
    have h := consCode_length_le b
    change (encode (listData bs)).length≤_ at ih
    omega
noncomputable def total (d : Digits) : ℕ :=
  2*Compile.bound program d.bits (limit d)
 theorem total_formula (d : Digits) :
    total d=2*(3*d.bits.length+8+limit d*(4*(d.bits.length+limit d)+16)) := by
  have hs : storeSize (RegisterBits.initial program d.bits).stack=d.bits.length := by
    simp [storeSize,RegisterBits.initial,Fin.sum_univ_succ]
  simp only [total,Compile.bound,Compile.overhead,hs]
 theorem total_bound : PolyBound DetPreparation.resource (total) := by
  have hl := DetPreparation.input_bound.mono digits_length
  have hn := limit_bound
  apply ((PolyBound.const _ 2).mul
    ((((PolyBound.const _ 3).mul hl).add (PolyBound.const _ 8)).add
      (hn.mul ((((PolyBound.const _ 4).mul (hl.add hn)).add (PolyBound.const _ 16)))))).mono
  intro d
  rw [total_formula]
 theorem resource_quasi (d : Digits) :
    DetPreparation.resource d+1≤2^(25003*(Nat.clog 2 (d.bits.length+2))^2) := by
  let h := Nat.clog 2 (d.bits.length+2)
  have hh : 1≤h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1<2)).mpr
    simp only [pow_zero]
    omega
  have hl : d.bits.length≤2^h := (Nat.le_add_right _ 2).trans (Nat.le_pow_clog (by norm_num) _)
  have he : h≤25000*h^2 := by nlinarith only [hh]
  have hp := hl.trans (Nat.pow_le_pow_right (by norm_num : 1≤2) he)
  have hx : treeSize (encode d)≤4*d.bits.length+1 := by
    change treeSize (listTree boolData d.bits)≤_
    rw [Halve.listTree_boolData]
    exact list_size _
  have hpos : 1≤2^(25000*h^2) := Nat.one_le_pow _ _ (by norm_num)
  calc
    DetPreparation.resource d+1≤8*2^(25000*h^2) := by
      unfold DetPreparation.resource
      rw [DetPreparation.exponent_length]
      change treeSize (encode d)+2^(25000*h^2)+1≤_
      omega
    _ = 2^(25000*h^2+3) := by rw [pow_add]; ring
    _ ≤ 2^(25003*h^2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hh])
 theorem polynomial_quasi {f : Digits→ℕ} (hf : PolyBound DetPreparation.resource f) :
    ∃ C : ℕ, ∀ d, f d≤2^(C*(Nat.clog 2 (d.bits.length+2))^2) := by
  obtain ⟨K,e,hf⟩ := hf
  refine ⟨K+25003*e,fun d => ?_⟩
  let h := Nat.clog 2 (d.bits.length+2)
  have hh : 1≤h := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1<2)).mpr
    simp only [pow_zero]
    omega
  have hk : K≤2^K := Nat.lt_two_pow_self.le
  calc
    f d ≤ K*(DetPreparation.resource d+1)^e := hf d
    _ ≤ 2^K*(2^(25003*h^2))^e := Nat.mul_le_mul hk (Nat.pow_le_pow_left (resource_quasi d) e)
    _ = 2^(K+25003*h^2*e) := by rw [←pow_mul,pow_add]
    _ ≤ 2^((K+25003*e)*h^2) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hs : 1≤h^2 := by nlinarith
      have hm := Nat.mul_le_mul_left K hs
      nlinarith only [hm]
 theorem natural_quasi_real {f : Digits→ℕ} (C : ℕ)
    (hf : ∀ d, f d≤2^(C*(Nat.clog 2 (d.bits.length+2))^2)) :
    ∃ D : ℝ, 0<D ∧ ∀ d, (f d : ℝ)≤(2 : ℝ)^(D*(Real.logb 2 (d.bits.length+2))^2) := by
  refine ⟨4*C+1,by positivity,fun d => ?_⟩
  have hc := clog_real_le_twice_logb d.bits.length
  have hc0 : (0 : ℝ)≤(Nat.clog 2 (d.bits.length+2) : ℝ) := Nat.cast_nonneg _
  have hl0 : 0≤Real.logb 2 (d.bits.length+2) := by linarith only [hc,hc0]
  have hs : ((Nat.clog 2 (d.bits.length+2) : ℝ))^2≤4*(Real.logb 2 (d.bits.length+2))^2 := by
    nlinarith only [hc,hc0,hl0]
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg C : (0 : ℝ)≤C)
  have hb : (f d : ℝ)≤(2 : ℝ)^(C*(Nat.clog 2 (d.bits.length+2))^2) := by exact_mod_cast hf d
  apply hb.trans
  rw [←Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
  simp only [Nat.cast_mul,Nat.cast_pow]
  nlinarith only [hm,sq_nonneg (Real.logb 2 (d.bits.length+2))]
 theorem total_quasi : ∃ C : ℝ, 0<C ∧ ∀ d,
    (total d : ℝ)≤(2 : ℝ)^(C*(Real.logb 2 (d.bits.length+2))^2) := by
  obtain ⟨C,hC⟩ := polynomial_quasi (total_bound)
  exact natural_quasi_real C hC
end MeanPayoff.DetRealizer

end OAI
