import OAI.Computability.MeanPayoff.Driver

namespace OAI

namespace MeanPayoff.TreeDevice.Certified.DetDriver
open BinaryData DetRaw

noncomputable def advance (ar : RawBasic.Arena) (s : State) : State := step (ar,s)
def Exec (ar : RawBasic.Arena) (s t : State) (k : ℕ) : Prop := (advance ar)^[k] s=t

theorem Exec.refl (ar : RawBasic.Arena) (s : State) : Exec ar s s 0 := rfl
theorem Exec.one (ar : RawBasic.Arena) (s : State) : Exec ar s (step (ar,s)) 1 := rfl
theorem Exec.trans {ar : RawBasic.Arena} {s t u : State} {k l : ℕ}
    (hs : Exec ar s t k) (ht : Exec ar t u l) : Exec ar s u (k+l) := by
  unfold Exec at *
  rw [Nat.add_comm, Function.iterate_add_apply, hs, ht]

variable {n d : ℕ} {A a b : Fin n → ℚ}

theorem down_pass {n d : ℕ} {A : Fin n → ℤ} {a b : Fin n → ℚ} {x : Input}
    (h : Rep A d a b x) (hd : 12≤d) (ar : RawBasic.Arena)
    (o : Label.Grid n → Fin n → Bool) (T : ℕ)
    (ho : ∀ (g : Label.Grid n) (vs : List W), VectorRep (Label.gridPivot A ((2:ℤ)^(d-12)) g) vs →
      ∀ ks : List Frame, ∃ k, k+1≤T ∧
        Exec ar (call (child false (x,vs)) ks) (ret (List.ofFn (o g)) ks) k)
    (g : Label.Grid n) (vs ds : List W) (hv : VectorRep (Label.gridPivot A ((2:ℤ)^(d-12)) g) vs)
    (ks : List Frame) :
    ∃ us k, VectorRep (Label.gridPivot A ((2:ℤ)^(d-12)) (Label.downRun o g).val.1) us ∧
      k≤(Label.downRank g+1)*T ∧
      Exec ar (call (child false (x,vs)) (frame 0 x ds vs::ks))
        (call (child true (x,us)) (frame 1 x us us::ks)) k := by
  let g' := Label.gridDown g (o g)
  let us := down (x,vs,List.ofFn (o g))
  have hu : VectorRep (Label.gridPivot A ((2:ℤ)^(d-12)) g') us := by
    rw [Label.gridPivot_down A (by positivity)]
    exact down_rep h hd hv (o g)
  have hc : different (us,vs)=decide (g'≠g) := by
    rw [different_eq hu hv]
    exact decide_eq_decide.mpr (not_congr (Label.gridPivot_injective A (by positivity)).eq_iff)
  obtain ⟨j,hj,hjexec⟩ := ho g vs hv (frame 0 x ds vs::ks)
  by_cases he : g'=g
  · refine ⟨us,j+1,?_,?_,?_⟩
    · rw [Label.downRun_fixed o g he]
      simpa only [he] using hu
    · exact hj.trans (Nat.le_mul_of_pos_left _ (by omega))
    · apply hjexec.trans
      have heq : step (ar,ret (List.ofFn (o g)) (frame 0 x ds vs::ks))=
          call (child true (x,us)) (frame 1 x us us::ks) := by
        rw [step_down]
        change (if different (us,vs) then _ else _)=_
        rw [hc,ite_eq_right (by simp [he])]
      simpa only [heq] using Exec.one ar (ret (List.ofFn (o g)) (frame 0 x ds vs::ks))
  · obtain ⟨zs,k,hz,hk,hkexec⟩ := down_pass h hd ar o T ho g' us ds hu ks
    refine ⟨zs,(j+1)+k,?_,?_,?_⟩
    · rw [Label.downRun_next o g he]
      exact hz
    · have hr : Label.downRank g'+1≤Label.downRank g :=
        Label.downRank_strict (Label.gridDown_le g (o g)) he
      have hm := Nat.mul_le_mul_right T hr
      nlinarith
    · apply Exec.trans (t:=call (child false (x,us)) (frame 0 x ds us::ks))
      · apply hjexec.trans
        have heq : step (ar,ret (List.ofFn (o g)) (frame 0 x ds vs::ks))=
            call (child false (x,us)) (frame 0 x ds us::ks) := by
          rw [step_down]
          change (if different (us,vs) then _ else _)=_
          rw [hc,ite_eq_left (by simpa using he)]
        simpa only [heq] using Exec.one ar (ret (List.ofFn (o g)) (frame 0 x ds vs::ks))
      · exact hkexec
termination_by Label.downRank g
decreasing_by exact Label.downRank_strict (Label.gridDown_le g (o g)) he

theorem up_pass {n d : ℕ} {A : Fin n → ℤ} {a b : Fin n → ℚ} {x : Input}
    (h : Rep A d a b x) (hd : 12≤d) (ar : RawBasic.Arena)
    (o : Label.Grid n → Fin n → Bool) (T : ℕ)
    (ho : ∀ (g : Label.Grid n) (vs : List W), VectorRep (Label.gridPivot A ((2:ℤ)^(d-12)) g) vs →
      ∀ ks : List Frame, ∃ k, k+1≤T ∧
        Exec ar (call (child true (x,vs)) ks) (ret (List.ofFn (o g)) ks) k)
    (g : Label.Grid n) (vs ds : List W) (hv : VectorRep (Label.gridPivot A ((2:ℤ)^(d-12)) g) vs)
    (ks : List Frame) :
    ∃ us k, VectorRep (Label.gridPivot A ((2:ℤ)^(d-12)) (Label.upRun o g).val.1) us ∧
      k≤(Label.upRank g+1)*T ∧
      Exec ar (call (child true (x,vs)) (frame 1 x ds vs::ks))
        (call (provisional (x,us)) (frame 2 x ds us::ks)) k := by
  let g' := Label.gridUp g (o g)
  let us := up (x,vs,List.ofFn (o g))
  have hu : VectorRep (Label.gridPivot A ((2:ℤ)^(d-12)) g') us := by
    rw [Label.gridPivot_up A (by positivity)]
    exact up_rep h hd hv (o g)
  have hc : different (us,vs)=decide (g'≠g) := by
    rw [different_eq hu hv]
    exact decide_eq_decide.mpr (not_congr (Label.gridPivot_injective A (by positivity)).eq_iff)
  obtain ⟨j,hj,hjexec⟩ := ho g vs hv (frame 1 x ds vs::ks)
  by_cases he : g'=g
  · refine ⟨us,j+1,?_,?_,?_⟩
    · rw [Label.upRun_fixed o g he]
      simpa only [he] using hu
    · exact hj.trans (Nat.le_mul_of_pos_left _ (by omega))
    · apply hjexec.trans
      have heq : step (ar,ret (List.ofFn (o g)) (frame 1 x ds vs::ks))=
          call (provisional (x,us)) (frame 2 x ds us::ks) := by
        rw [step_up]
        change (if different (us,vs) then _ else _)=_
        rw [hc,ite_eq_right (by simp [he])]
      simpa only [heq] using Exec.one ar (ret (List.ofFn (o g)) (frame 1 x ds vs::ks))
  · obtain ⟨zs,k,hz,hk,hkexec⟩ := up_pass h hd ar o T ho g' us ds hu ks
    refine ⟨zs,(j+1)+k,?_,?_,?_⟩
    · rw [Label.upRun_next o g he]
      exact hz
    · have hr : Label.upRank g'+1≤Label.upRank g :=
        Label.upRank_strict (Label.le_gridUp g (o g)) he
      have hm := Nat.mul_le_mul_right T hr
      nlinarith
    · apply Exec.trans (t:=call (child true (x,us)) (frame 1 x ds us::ks))
      · apply hjexec.trans
        have heq : step (ar,ret (List.ofFn (o g)) (frame 1 x ds vs::ks))=
            call (child true (x,us)) (frame 1 x ds us::ks) := by
          rw [step_up]
          change (if different (us,vs) then _ else _)=_
          rw [hc,ite_eq_left (by simpa using he)]
        simpa only [heq] using Exec.one ar (ret (List.ofFn (o g)) (frame 1 x ds vs::ks))
      · exact hkexec
termination_by Label.upRank g
decreasing_by exact Label.upRank_strict (Label.le_gridUp g (o g)) he

end MeanPayoff.TreeDevice.Certified.DetDriver

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Size
@[simp] theorem pair {α β : Type} [Encoding α] [Encoding β] (x : α) (y : β) :
    treeSize (encode (x,y))=treeSize (encode x)+treeSize (encode y)+1 := by
  change treeSize (product encode encode (x,y))=_
  simp only [product,treeSize_pair]
theorem bool (b : Bool) : treeSize (encode b)≤5 := by cases b <;> decide
theorem list_bound {α : Type} [Encoding α] {xs : List α} {M : ℕ}
    (h : ∀ x∈xs, treeSize (encode x)≤M) : treeSize (encode xs)≤xs.length*(M+1)+1 := by
  induction xs with
  | nil => change 1≤0*(M+1)+1; omega
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    change treeSize (listTree encode (x::xs))≤_
    rw [listTree,treeSize_pair,List.length_cons]
    change treeSize (listTree encode xs)≤_ at ht
    nlinarith
theorem unit_list (xs : Count) : treeSize (encode xs)≤2*xs.length+1 := by
  have h := list_bound (xs:=xs) (M:=1) (by intro x _; rfl)
  omega
theorem bool_list (xs : List Bool) : treeSize (encode xs)≤6*xs.length+1 := by
  have h := list_bound (xs:=xs) (M:=5) (by intro x _; exact bool x)
  omega
end Size

namespace Array
 theorem Small.size {n M : ℕ} {xs : List W} (h : Small n M xs) :
    treeSize (encode xs)≤n*(4*M+6)+1 :=
  (size_bound h.digits).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h.length) 1)
 theorem small_of_size {S : ℕ} (xs : List W) (h : treeSize (encode xs)≤S) : Small S S xs :=
  ⟨(Size.length xs).trans h,(bounded_size xs).mono h⟩
end Array

namespace DetMass
 theorem small_of_size {S : ℕ} (x : Data) (h : treeSize (encode x)≤S) : Small S S x :=
  ⟨(digits_le_wordSize x.1).trans ((Size.fst x).trans h),Array.small_of_size x.2 ((Size.snd x).trans h)⟩
 theorem Small.size {n M : ℕ} {x : Data} (h : Small n M x) :
    treeSize (encode x)≤20*(n+1)*(M+1) := by
  have ha := h.nums.size
  have hw := wordSize_bound x.1
  have hd := h.den
  rcases x with ⟨w,ws⟩
  rw [Size.pair]
  dsimp only at ha hd
  change treeSize (encode w)≤4*w.digits.length+5 at hw
  nlinarith
end DetMass

namespace DetRaw
 theorem small_of_size {S : ℕ} (x : Input) (h : treeSize (encode x)≤S) : Small S S x := by
  have h1 := (Size.fst x).trans h
  have h2 := (Size.snd x).trans h
  exact ⟨(digits_le_wordSize x.1.1).trans ((Size.fst x.1).trans h1),
    Array.small_of_size x.1.2 ((Size.snd x.1).trans h1),
    DetMass.small_of_size x.2.1 ((Size.fst x.2).trans h2),
    DetMass.small_of_size x.2.2 ((Size.snd x.2).trans h2)⟩
 theorem Small.size {n M : ℕ} {x : Input} (h : Small n M x) :
    treeSize (encode x)≤100*(n+1)*(M+1) := by
  have ha := h.lower.size
  have hw := wordSize_bound x.1.1
  have hd := h.width
  have hb := h.a.size
  have hc := h.b.size
  rcases x with ⟨⟨w,ws⟩,a,b⟩
  simp only [Size.pair]
  dsimp only at ha hd hb hc
  change treeSize (encode w)≤4*w.digits.length+5 at hw
  nlinarith
end DetRaw

namespace DetDriver
 theorem FrameSmall.size {n M : ℕ} {f : Frame} (h : FrameSmall n M f) :
    treeSize (encode f)≤200*(n+1)*(M+1) := by
  have ht := (Size.unit_list f.1).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h.tag) 1)
  have hi := h.input.size
  have hd := h.down.size
  have hv := h.pivot.size
  rcases f with ⟨t,x,ds,vs⟩
  simp only [Size.pair]
  nlinarith
 theorem frameSmall_of_size {S : ℕ} (f : Frame) (h : treeSize (encode f)≤S) : FrameSmall S S f := by
  have h1 := (Size.snd f).trans h
  have h2 := (Size.snd f.2).trans h1
  exact ⟨(Size.length f.1).trans ((Size.fst f).trans h),
    DetRaw.small_of_size f.2.1 ((Size.fst f.2).trans h1),
    Array.small_of_size f.2.2.1 ((Size.fst f.2.2).trans h2),
    Array.small_of_size f.2.2.2 ((Size.snd f.2.2).trans h2)⟩
 theorem Small.size {n M K : ℕ} {s : State} (h : Small n M K s) :
    treeSize (encode s)≤400*(n+1)*(M+1)*(K+1) := by
  have hb := Size.bool s.1.1
  have hi := h.input.size
  have hl := (Size.bool_list s.1.2.2).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 6 h.labels) 1)
  have hf := Size.list_bound (fun f hf => (h.frames f hf).size)
  have hk := h.depth
  have hfs : treeSize (encode s.2)≤K*(200*(n+1)*(M+1)+1)+1 :=
    hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1)
  rcases s with ⟨⟨b,x,ls⟩,ks⟩
  simp only [Size.pair]
  nlinarith [Nat.zero_le (n*M*K),Nat.zero_le (n*K),Nat.zero_le (M*K)]
 theorem small_of_size {S : ℕ} (s : State) (h : treeSize (encode s)≤S) : Small S S S s := by
  have h1 := (Size.fst s).trans h
  have h2 := (Size.snd s.1).trans h1
  have h3 := (Size.snd s).trans h
  exact ⟨DetRaw.small_of_size s.1.2.1 ((Size.fst s.1.2).trans h2),
    (Size.length s.1.2.2).trans ((Size.snd s.1.2).trans h2),
    (Size.length s.2).trans h3,fun f hf => frameSmall_of_size f ((Size.mem hf).trans h3)⟩
 theorem iterate_small {n M K : ℕ} {s : State} (hn : 3≤n) (h : Small n M K s)
    (ar : RawBasic.Arena) (k : ℕ) : Small n (M+100*k) (K+k) ((advance ar)^[k] s) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hs := step_small hn ih ar
    simpa only [Nat.mul_succ,Nat.add_assoc,advance] using hs

local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
noncomputable def tick : Code (Env×Unit) Env := fst ≫ₚ (arena ⋏ₚ step)
@[simp] theorem tick_eval (e : Env) (u : Unit) : tick (e,u)=(e.1,advance e.1 e.2) := rfl
 theorem fold_tick (e : Env) (xs : Count) :
    Fold.fold tick.eval e xs=(e.1,(advance e.1)^[xs.length] e.2) := by
  induction xs generalizing e with
  | nil => rfl
  | cons u xs ih =>
    change Fold.fold tick.eval (tick (e,u)) xs=_
    rw [tick_eval,ih]
    simp only [List.length_cons,Function.iterate_succ_apply]
 theorem tick_prefix (e : Env) (xs : Count) (k : ℕ) (hk : k≤xs.length) :
    treeSize (encode (Fold.fold tick.eval e (xs.take k)))≤1000000*(treeSize (encode (e,xs))+1)^3 := by
  let P := treeSize (encode (e,xs))+1
  have hp : 1≤P := by dsimp [P]; omega
  have he : treeSize (encode e)≤P := (Size.fst (e,xs)).trans (by dsimp [P]; omega)
  have hs : treeSize (encode e.2)≤3*P := (Size.snd e).trans (he.trans (by omega))
  have ha : treeSize (encode e.1)≤P := (Size.fst e).trans he
  have hx : xs.length≤P := (Size.length xs).trans ((Size.snd (e,xs)).trans (by dsimp [P]; omega))
  have hg := iterate_small (show 3≤3*P by omega) (small_of_size e.2 hs) e.1 k
  have hgg := hg.mono (show 3*P+100*k≤103*P by omega) (show 3*P+k≤4*P by omega)
  have hz := hgg.size
  have hprod : 400*(3*P+1)*(103*P+1)*(4*P+1)≤832000*P^3 := by
    calc
      _≤400*(4*P)*(104*P)*(5*P) := by gcongr <;> omega
      _=832000*P^3 := by ring
  rw [fold_tick,List.length_take,Nat.min_eq_left hk,Size.pair]
  change _≤1000000*P^3
  have hp3 : P≤P^3 := by nlinarith [Nat.mul_self_le_mul_self hp]
  nlinarith
noncomputable def run : Code (Env×Count) Env := foldPrefix tick 1000000 3 tick_prefix
@[simp] theorem run_eval (e : Env) (xs : Count) : run (e,xs)=(e.1,(advance e.1)^[xs.length] e.2) := fold_tick e xs
end DetDriver
end MeanPayoff.TreeDevice.Certified

end OAI
