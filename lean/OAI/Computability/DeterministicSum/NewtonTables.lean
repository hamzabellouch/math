import Mathlib
import OAI.Computability.DeterministicSum.ModularInverses

namespace OAI

/-! Prime-power coefficient tables and their paid Newton transforms. -/

namespace DeterministicThreeSum.Newton
open Finset
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] {q : ℕ}

lemma entry_map (node : Fin q → ℤ) :
    (Int.castRingHom R).mapMatrix (entry node)=entry (fun i => (node i:R)) := by
  ext i j
  simp [entry]

lemma cast_natAbs_unit {a : ℤ} (h : IsUnit (a:R)) : IsUnit ((a.natAbs:ℕ):R) := by
  have he : ((a.natAbs:ℕ):R)=((|a|:ℤ):R) := by
    rw [show ((a.natAbs:ℕ):R)=((a.natAbs:ℤ):R) by simp,Int.natCast_natAbs]
  rw [he]
  rcases abs_choice a with hpos|hneg
  · rwa [hpos]
  · simpa only [hneg,Int.cast_neg] using h.neg

def inverseDenominator (order : Equiv.Perm (Fin q)) : ℕ :=
  (entry (fun i => ((order i).val:ℤ))).det.natAbs

def inverseNumerator (order : Equiv.Perm (Fin q)) (i j : Fin q) : ℤ :=
  (entry (fun k => ((order k).val:ℤ))).det.sign *
    (entry (fun k => ((order k).val:ℤ))).adjugate i j

lemma inverseDenominator_unit {p e : ℕ} (hp : p.Prime) (he : 0 < e) (hq : q < p)
    (order : Equiv.Perm (Fin q)) : IsUnit (inverseDenominator order:ZMod (p^e)) := by
  apply cast_natAbs_unit
  have h:=entry_det_unit (fun i => ((order i).val:ZMod (p^e))) (primePower_node_units hp he hq order)
  have hmap : (Int.castRingHom (ZMod (p^e))).mapMatrix (entry (fun i => ((order i).val:ℤ)))=
      entry (fun i => ((order i).val:ZMod (p^e))) := by
    simpa only [Int.cast_natCast] using entry_map (R:=ZMod (p^e)) (fun i => ((order i).val:ℤ))
  have hd:=RingHom.map_det (Int.castRingHom (ZMod (p^e))) (entry (fun i => ((order i).val:ℤ)))
  rw [hmap] at hd
  change IsUnit ((Int.castRingHom (ZMod (p^e))) (entry (fun i => ((order i).val:ℤ))).det)
  rwa [hd]

lemma inverseDenominator_prime {p : ℕ} (hp : p.Prime) (hq : q < p) (order : Equiv.Perm (Fin q)) :
    ¬p∣inverseDenominator order := by
  have h:=inverseDenominator_unit (e:=1) hp (by omega) hq order
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0<1)).mp h

lemma inverseInteger_eq (M : Matrix (Fin q) (Fin q) ℤ) (s : R)
    (hs : s*(M.det.natAbs:R)=1) :
    ((Int.castRingHom R).mapMatrix M)⁻¹=
      (s*(M.det.sign:R)) • (Int.castRingHom R).mapMatrix M.adjugate := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul,RingHom.map_adjugate,Matrix.adjugate_mul,← RingHom.map_det,smul_smul]
  have hz : (M.det.sign:R)*(M.det:R)=(M.det.natAbs:R) := by
    rw [← Int.cast_mul,Int.sign_mul_self,Int.cast_natCast]
  change ((s*(M.det.sign:R))*(M.det:R)) • (1:Matrix (Fin q) (Fin q) R)=1
  rw [mul_assoc,hz,hs,one_smul]

lemma inverse_entry_integer (order : Equiv.Perm (Fin q)) (s : R)
    (hs : s*(inverseDenominator order:R)=1) (i j : Fin q) :
    ((entry (fun k => ((order k).val:R)))⁻¹) i j=s*(inverseNumerator order i j:R) := by
  have hm:=inverseInteger_eq (entry (fun k => ((order k).val:ℤ))) s hs
  rw [entry_map] at hm
  have hv:=congrArg (fun A : Matrix (Fin q) (Fin q) R => A i j) hm
  simpa [inverseNumerator,Int.cast_mul,mul_assoc] using hv

end
end DeterministicThreeSum.Newton
namespace DeterministicThreeSum.Structured.Indexed.NewtonTable
open Command DeterministicThreeSum.Newton
noncomputable section

def numeratorAt {q : ℕ} (order : Equiv.Perm (Fin q)) (z : ℕ) : ℤ :=
  if h : z<q*q then
    inverseNumerator order
      ⟨z/q,(Nat.div_lt_iff_lt_mul (by nlinarith : 0<q)).mpr h⟩
      ⟨z%q,Nat.mod_lt _ (by nlinarith : 0<q)⟩
  else 0

def numerators {q : ℕ} (order : Equiv.Perm (Fin q)) : List ℤ :=
  List.ofFn (fun z : Fin (q*q) => numeratorAt order z.val)

def command {q : ℕ} (p : ℕ) (order : Equiv.Perm (Fin q)) : Command :=
  commonTable p (inverseDenominator order) (numerators order)

lemma numeratorAt_entry {q : ℕ} (order : Equiv.Perm (Fin q)) (i j : Fin q) :
    numeratorAt order (i.val*q+j.val)=inverseNumerator order i j := by
  have hq : 0<q := Nat.zero_lt_of_lt i.isLt
  have hi : i.val*q+j.val<q*q := by nlinarith [i.isLt,j.isLt]
  unfold numeratorAt
  rw [dite_eq_left hi]
  congr 1 <;> apply Fin.ext
  · change (i.val*q+j.val)/q=i.val
    rw [Nat.mul_comm i.val q,Nat.mul_add_div hq,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  · simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]

theorem command_correct {w p e q base : ℕ} (order : Equiv.Perm (Fin q)) (s : Data)
    (hp : p.Prime) (hq : q<p)
    (hmul : (p^(e+1))*(p^(e+1))<wordModulus w)
    (hD : inverseDenominator order<wordModulus w)
    (hbase : base+q*q<wordModulus w)
    (hints : ∀ a∈numerators order, a.natAbs<wordModulus w)
    (h2 : s.registers 2=p^(e+1)) (h3 : s.registers 3=base) :
    ∃ cost z, Eval w (command p order) s cost z ∧ cost≤10*w+13+9*(q*q) ∧
      (∀ i j : Fin q, ∃ v, z.memory (base+i.val*q+j.val)=some v ∧ v<p^(e+1) ∧
        (v:ZMod (p^(e+1)))=((entry (fun k => ((order k).val:ZMod (p^(e+1)))))⁻¹) i j) ∧
      (∀ a, a<base ∨ base+q*q≤a → z.memory a=s.memory a) ∧
      (∀ r, r=2 ∨ r=3 ∨ 7≤r → z.registers r=s.registers r) := by
  have hl : (numerators order).length=q*q := by simp [numerators]
  obtain ⟨c,z,he,hc,hm,houtside,hframe⟩:=commonTable_correct s (numerators order) hp hmul hD
    (inverseDenominator_prime hp hq order) (by simpa only [hl] using hbase) hints h2 h3
  refine ⟨c,z,he,by simpa only [hl] using hc,?_,by simpa only [hl] using houtside,hframe⟩
  intro i j
  have hi : i.val*q+j.val<q*q := by nlinarith [i.isLt,j.isLt]
  obtain ⟨v,hv,hvT,hvalue⟩:=hm (i.val*q+j.val) (by simpa only [hl] using hi)
  refine ⟨v,by simpa only [Nat.add_assoc] using hv,hvT,?_⟩
  have hu:=inverseDenominator_unit hp (by omega : 0<e+1) hq order
  obtain ⟨a,ha⟩:=hu.exists_left_inv
  rw [inverse_entry_integer order a ha]
  have hnum : (numerators order)[i.val*q+j.val]=inverseNumerator order i j := by
    simpa only [numerators,List.getElem_ofFn] using numeratorAt_entry order i j
  rw [hnum] at hvalue
  calc
    (v:ZMod (p^(e+1))) = a*((v:ZMod (p^(e+1)))*(inverseDenominator order:ZMod (p^(e+1)))) := by calc
      _ = (v:ZMod (p^(e+1)))*(a*(inverseDenominator order:ZMod (p^(e+1)))) := by rw [ha,mul_one]
      _ = _ := by ring
    _ = _ := by rw [hvalue]
end
end DeterministicThreeSum.Structured.Indexed.NewtonTable
namespace DeterministicThreeSum.Newton
open Finset
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R] {q : ℕ}

lemma univariate_integer (node : Fin q → ℤ) (j : Fin q) :
    Polynomial.map (Int.castRingHom R) (univariate node j)=univariate (fun k => (node k:R)) j := by
  simp [univariate,Polynomial.map_prod]

lemma conversion_integer (node : Fin q → ℤ) (j v : Fin q) :
    ((conversion node j v:ℤ):R)=conversion (fun k => (node k:R)) j v := by
  change (Int.castRingHom R) ((univariate node j).coeff v.val)=_
  rw [← Polynomial.coeff_map,univariate_integer]
  rfl
end
end DeterministicThreeSum.Newton
namespace DeterministicThreeSum.Structured.Indexed.NewtonConversionTable
open Command DeterministicThreeSum.Newton
noncomputable section

def integerAt {q : ℕ} (order : Equiv.Perm (Fin q)) (z : ℕ) : ℤ :=
  if h : z<q*q then
    conversion (fun k => ((order k).val:ℤ))
      ⟨z%q,Nat.mod_lt _ (by nlinarith : 0<q)⟩
      ⟨z/q,(Nat.div_lt_iff_lt_mul (by nlinarith : 0<q)).mpr h⟩
  else 0

def integers {q : ℕ} (order : Equiv.Perm (Fin q)) : List ℤ :=
  List.ofFn (fun z : Fin (q*q) => integerAt order z.val)

def command {q : ℕ} (p : ℕ) (order : Equiv.Perm (Fin q)) : Command :=
  commonTable p 1 (integers order)

lemma integerAt_entry {q : ℕ} (order : Equiv.Perm (Fin q)) (i j : Fin q) :
    integerAt order (i.val*q+j.val)=conversion (fun k => ((order k).val:ℤ)) j i := by
  have hq : 0<q := Nat.zero_lt_of_lt i.isLt
  have hi : i.val*q+j.val<q*q := by nlinarith [i.isLt,j.isLt]
  unfold integerAt
  rw [dite_eq_left hi]
  congr 1 <;> apply Fin.ext
  · simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  · change (i.val*q+j.val)/q=i.val
    rw [Nat.mul_comm i.val q,Nat.mul_add_div hq,Nat.div_eq_of_lt j.isLt,Nat.add_zero]

theorem command_correct {w p e q base : ℕ} (order : Equiv.Perm (Fin q)) (s : Data)
    (hp : p.Prime) (hmul : (p^(e+1))*(p^(e+1))<wordModulus w)
    (hbase : base+q*q<wordModulus w)
    (hints : ∀ a∈integers order, a.natAbs<wordModulus w)
    (h2 : s.registers 2=p^(e+1)) (h3 : s.registers 3=base) :
    ∃ cost z, Eval w (command p order) s cost z ∧ cost≤10*w+13+9*(q*q) ∧
      (∀ i j : Fin q, ∃ v, z.memory (base+i.val*q+j.val)=some v ∧ v<p^(e+1) ∧
        (v:ZMod (p^(e+1)))=conversion (fun k => ((order k).val:ZMod (p^(e+1)))) j i) ∧
      (∀ a, a<base ∨ base+q*q≤a → z.memory a=s.memory a) ∧
      (∀ r, r=2 ∨ r=3 ∨ 7≤r → z.registers r=s.registers r) := by
  have hT : 1≤p^(e+1) := Nat.one_le_pow _ _ hp.pos
  have h1 : 1<wordModulus w := by nlinarith
  have hl : (integers order).length=q*q := by simp [integers]
  obtain ⟨c,z,he,hc,hm,houtside,hframe⟩:=commonTable_correct s (integers order) hp hmul h1
    (by exact hp.not_dvd_one) (by simpa only [hl] using hbase) hints h2 h3
  refine ⟨c,z,he,by simpa only [hl] using hc,?_,by simpa only [hl] using houtside,hframe⟩
  intro i j
  have hi : i.val*q+j.val<q*q := by nlinarith [i.isLt,j.isLt]
  obtain ⟨v,hv,hvT,hvalue⟩:=hm (i.val*q+j.val) (by simpa only [hl] using hi)
  refine ⟨v,by simpa only [Nat.add_assoc] using hv,hvT,?_⟩
  have hnum : (integers order)[i.val*q+j.val]=conversion (fun k => ((order k).val:ℤ)) j i := by
    simpa only [integers,List.getElem_ofFn] using integerAt_entry order i j
  rw [hnum] at hvalue
  have hi':=((conversion_integer (R:=ZMod (p^(e+1))) (fun k => ((order k).val:ℤ)) j i))
  simpa only [Nat.cast_one,mul_one,hi',Int.cast_natCast] using hvalue
end
end DeterministicThreeSum.Structured.Indexed.NewtonConversionTable
namespace DeterministicThreeSum.Structured.Indexed.NewtonPass
open Command Axis DeterministicThreeSum.Newton
noncomputable section

lemma inverseTable_lt {T q : ℕ} (hT : 0<T) (node : Fin q → ZMod T) (z : ℕ) :
    inverseTable T q node z<T := by
  let : NeZero T := ⟨by omega⟩
  unfold inverseTable
  split_ifs <;> simp only [ZMod.val_lt, hT]

lemma conversionTable_lt {T q : ℕ} (hT : 0<T) (node : Fin q → ZMod T) (z : ℕ) :
    conversionTable T q node z<T := by
  let : NeZero T := ⟨by omega⟩
  unfold conversionTable
  split_ifs <;> simp only [ZMod.val_lt,hT]

lemma memory_inverse {T q base : ℕ} (hT : 0<T) (hq : 0<q) (node : Fin q → ZMod T) (s : Data)
    (h : ∀ i j : Fin q, ∃ v, s.memory (base+i.val*q+j.val)=some v ∧ v<T ∧
      (v:ZMod T)=((entry node)⁻¹) i j) :
    ∀ z, z<q*q → s.memory (base+z)=some (inverseTable T q node z) ∧ inverseTable T q node z<T := by
  let : NeZero T := ⟨by omega⟩
  intro z hz
  let i : Fin q := ⟨z/q,(Nat.div_lt_iff_lt_mul hq).mpr hz⟩
  let j : Fin q := ⟨z%q,Nat.mod_lt _ hq⟩
  have he : i.val*q+j.val=z := by dsimp [i,j]; nlinarith only [Nat.mod_add_div z q]
  obtain ⟨v,hv,hvT,hvc⟩:=h i j
  have hc : (v:ZMod T)=(inverseTable T q node z:ZMod T) := by
    rw [← he,inverseTable_entry hT]
    exact hvc
  apply_fun ZMod.val at hc
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hvT,
    Nat.mod_eq_of_lt (inverseTable_lt hT node z)] at hc
  refine ⟨?_,inverseTable_lt hT node z⟩
  simpa only [Nat.add_assoc,he,hc] using hv

lemma memory_conversion {T q base : ℕ} (hT : 0<T) (hq : 0<q) (node : Fin q → ZMod T) (s : Data)
    (h : ∀ i j : Fin q, ∃ v, s.memory (base+i.val*q+j.val)=some v ∧ v<T ∧
      (v:ZMod T)=conversion node j i) :
    ∀ z, z<q*q → s.memory (base+z)=some (conversionTable T q node z) ∧ conversionTable T q node z<T := by
  let : NeZero T := ⟨by omega⟩
  intro z hz
  let i : Fin q := ⟨z/q,(Nat.div_lt_iff_lt_mul hq).mpr hz⟩
  let j : Fin q := ⟨z%q,Nat.mod_lt _ hq⟩
  have he : i.val*q+j.val=z := by dsimp [i,j]; nlinarith only [Nat.mod_add_div z q]
  obtain ⟨v,hv,hvT,hvc⟩:=h i j
  have hc : (v:ZMod T)=(conversionTable T q node z:ZMod T) := by
    rw [← he,conversionTable_entry hT]
    exact hvc
  apply_fun ZMod.val at hc
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hvT,
    Nat.mod_eq_of_lt (conversionTable_lt hT node z)] at hc
  refine ⟨?_,conversionTable_lt hT node z⟩
  simpa only [Nat.add_assoc,he,hc] using hv

def tableSources (k b i : ℕ) : Operand := match i with
  | 2 => .register (k+6) | 3 => .register (k+b) | _ => .literal 0

def tableValues (T B i : ℕ) : ℕ := match i with
  | 2 => T | 3 => B | _ => 0

lemma tableSetup_correct {w k T B b : ℕ} (s : Data) (hk : 16≤k)
    (hT : T<wordModulus w) (hB : B<wordModulus w)
    (h6 : s.registers (k+6)=T) (hb : s.registers (k+b)=B) :
    Eval w (copyPrefix (tableSources k b) 4) s 4 (patched s 4 (tableValues T B)) := by
  apply copyPrefix_correct
  · intro i hi r hr
    interval_cases i <;> simp only [tableSources] at hr <;> cases hr <;> omega
  · intro i hi
    interval_cases i <;> simp [tableSources,tableValues,operand_register,operand_literal,
      h6,hb,Nat.mod_eq_of_lt hT,Nat.mod_eq_of_lt hB]

def initialSources (k i : ℕ) : Operand := match i with
  | 3 => .register (k+10) | 4 => .register (k+11) | 5 => .register (k+12)
  | _ => tensorSources k i

lemma initialSetup_correct {w k T N P S C B A : ℕ} (s : Data) (hk : 16≤k)
    (hT : T<wordModulus w) (hN : N<wordModulus w) (hP : P<wordModulus w)
    (hS : S<wordModulus w) (hC : C<wordModulus w) (hB : B<wordModulus w) (hA : A<wordModulus w)
    (h0 : s.registers k=A) (h1 : s.registers (k+1)=B) (h2 : s.registers (k+2)=N)
    (h12 : s.registers (k+12)=C) (h6 : s.registers (k+6)=T)
    (h10 : s.registers (k+10)=P) (h11 : s.registers (k+11)=S) :
    Eval w (copyPrefix (initialSources k) 8) s 8
      (patched s 8 (tensorValues T N P S C B A)) := by
  apply copyPrefix_correct
  · intro i hi r hr
    interval_cases i <;> simp only [initialSources,tensorSources] at hr <;> cases hr <;> omega
  · intro i hi
    interval_cases i <;> simp [initialSources,tensorSources,tensorValues,operand_register,operand_literal,
      h0,h1,h2,h12,h6,h10,h11,Nat.mod_eq_of_lt hT,Nat.mod_eq_of_lt hN,Nat.mod_eq_of_lt hP,
      Nat.mod_eq_of_lt hS,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt hB,Nat.mod_eq_of_lt hA]

def paidCommand {q : ℕ} (p k : ℕ) (order : Equiv.Perm (Fin q)) : Command :=
  .seq (copyPrefix (tableSources k 12) 4) (.seq (NewtonTable.command p order)
    (.seq (copyPrefix (tableSources k 5) 4) (.seq (NewtonConversionTable.command p order)
      (.seq (copyPrefix (initialSources k) 8) (command q k)))))
end
end DeterministicThreeSum.Structured.Indexed.NewtonPass
namespace DeterministicThreeSum.Structured.Indexed.NewtonPass
open Command Axis DeterministicThreeSum.Newton
noncomputable section

theorem paidCommand_correct {w p e q L d A P S C E D k : ℕ}
    (order : Equiv.Perm (Fin q)) (s : Data) (x : ℕ → ℕ)
    (hk : 16≤k) (hkw : (tensorCommand q q).writes.sup id<k)
    (hp : p.Prime) (hq : 1<q) (hqp : q<p) (hA : 0<A)
    (hadd : 2*(p^(e+1))<wordModulus w) (hmul : (p^(e+1))*(p^(e+1))<wordModulus w)
    (hL : A*q^d≤L) (hLw : L*q+L+3<wordModulus w)
    (hP : P+L+1<wordModulus w) (hS : S+L+1<wordModulus w)
    (hC : C+q*q<wordModulus w) (hE : E+q*q<wordModulus w) (hD : D<wordModulus w)
    (hPS : S+L≤P ∨ P+L≤S)
    (hCP : C+q*q≤P ∨ P+L≤C) (hCS : C+q*q≤S ∨ S+L≤C)
    (hEP : E+q*q≤P ∨ P+L≤E) (hES : E+q*q≤S ∨ S+L≤E)
    (hCE : E+q*q≤C ∨ C+q*q≤E)
    (hden : inverseDenominator order<wordModulus w)
    (hints : ∀ a∈NewtonTable.numerators order, a.natAbs<wordModulus w)
    (hconv : ∀ a∈NewtonConversionTable.integers order, a.natAbs<wordModulus w)
    (hctx : ∀ i, i<8 → s.registers (k+i)=context A (tensorStride q d) (A*q*tensorStride q d) (q^d) D E (p^(e+1)) i)
    (h10 : s.registers (k+10)=P) (h11 : s.registers (k+11)=S) (h12 : s.registers (k+12)=C)
    (hx : ∀ i, i<A*q^d → s.memory (S+i)=some (x i) ∧ x i<p^(e+1)) :
    ∃ cost z, Eval w (paidCommand p k order) s cost z ∧
      cost≤2*(((row q q).cost+5)*L+11)*d+(5*d+10)*(A*q^d)+20*w+18*(q*q)+61 ∧
      (∀ a : Fin 8, z.registers a.val=environment (p^(e+1)) 0 P S E 0 (A*q^d) 0 a) ∧
      (∀ i, i<A*q^d → z.memory (S+i)=some
        (tensorValue (p^(e+1)) q q (conversionTable (p^(e+1)) q (fun j => ((order j).val:ZMod (p^(e+1))))) d
          (filtered q d D (tensorValue (p^(e+1)) q q
            (inverseTable (p^(e+1)) q (fun j => ((order j).val:ZMod (p^(e+1))))) d x)) i)) ∧
      (∀ a, (a<P ∨ P+L≤a) → (a<S ∨ S+L≤a) →
        (a<C ∨ C+q*q≤a) → (a<E ∨ E+q*q≤a) → z.memory a=s.memory a) := by
  have hT : 0<p^(e+1) := pow_pos hp.pos _
  have hTw : p^(e+1)<wordModulus w := by omega
  have h6 : s.registers (k+6)=p^(e+1) := by simpa [context] using hctx 6 (by omega)
  have h5 : s.registers (k+5)=E := by simpa [context] using hctx 5 (by omega)
  let u := patched s 4 (tableValues (p^(e+1)) C)
  have eu := tableSetup_correct (w:=w) (k:=k) (T:=p^(e+1)) (B:=C) (b:=12) s hk hTw (by omega) h6 h12
  obtain ⟨c1,t1,et1,hc1,ht1m,ht1f,ht1r⟩:=NewtonTable.command_correct (w:=w) (p:=p) (e:=e) (base:=C)
    order u hp hqp hmul hden hC hints (by simp [u,patched,tableValues]) (by simp [u,patched,tableValues])
  have hr1 : ∀ i, t1.registers (k+i)=s.registers (k+i) := by
    intro i
    rw [ht1r _ (by omega)]
    simp [u,patched,show ¬k+i<4 by omega]
  let u1 := patched t1 4 (tableValues (p^(e+1)) E)
  have eu1 := tableSetup_correct (w:=w) (k:=k) (T:=p^(e+1)) (B:=E) (b:=5) t1 hk hTw (by omega)
    ((hr1 6).trans h6) ((hr1 5).trans h5)
  obtain ⟨c2,t2,et2,hc2,ht2m,ht2f,ht2r⟩:=NewtonConversionTable.command_correct (w:=w) (p:=p) (e:=e) (base:=E)
    order u1 hp hmul hE hconv (by simp [u1,patched,tableValues]) (by simp [u1,patched,tableValues])
  have hr2 : ∀ i, t2.registers (k+i)=s.registers (k+i) := by
    intro i
    rw [ht2r _ (by omega)]
    change (if k+i<4 then _ else t1.registers (k+i))=_
    rw [ite_eq_right (by omega),hr1]
  have hQpos : 0<q^d := pow_pos (by omega : 0<q) _
  have hQL : q^d≤L := (by simpa using Nat.mul_le_mul_right (q^d) hA : q^d≤A*q^d) |>.trans hL
  have hAw : A<wordModulus w := by
    have hh : A≤A*q^d := by simpa using Nat.mul_le_mul_left A hQpos
    omega
  have hBw : tensorStride q d<wordModulus w := (tensorStride_le hq d).trans_lt (by omega)
  have hNw : A*q*tensorStride q d<wordModulus w := (initialCount_le hq d).trans_lt (by omega)
  let u2 := patched t2 8 (tensorValues (p^(e+1)) (A*q*tensorStride q d) P S C (tensorStride q d) A)
  have eu2 := initialSetup_correct (w:=w) (k:=k) (T:=p^(e+1)) (N:=A*q*tensorStride q d)
    (P:=P) (S:=S) (C:=C) (B:=tensorStride q d) (A:=A) t2 hk hTw hNw (by omega) (by omega) (by omega) hBw hAw
    (by simpa only [Nat.add_zero] using (hr2 0).trans (by simpa [context] using hctx 0 (by omega)))
    ((hr2 1).trans (by simpa [context] using hctx 1 (by omega)))
    ((hr2 2).trans (by simpa [context] using hctx 2 (by omega)))
    ((hr2 12).trans h12) ((hr2 6).trans h6) ((hr2 10).trans h10) ((hr2 11).trans h11)
  have hu2r : ∀ a : Fin 8, u2.registers a.val=
      environment (p^(e+1)) (A*q*tensorStride q d) P S C (tensorStride q d) A 0 a := by
    intro a; simp only [u2,patched,a.isLt,ite_eq_left,tensorValues_environment]
  have hu2ctx : ∀ i, i<8 → u2.registers (k+i)=context A (tensorStride q d) (A*q*tensorStride q d) (q^d) D E (p^(e+1)) i := by
    intro i hi
    simp only [u2,patched,ite_eq_right (show ¬k+i<8 by omega),hr2,hctx i hi]
  let node : Fin q → ZMod (p^(e+1)) := fun j => ((order j).val:ZMod (p^(e+1)))
  have hu2c : ∀ i, i<q*q → u2.memory (C+i)=some (inverseTable (p^(e+1)) q node i) ∧ inverseTable (p^(e+1)) q node i<p^(e+1) := by
    intro i hi
    change t2.memory _=_ ∧ _
    rw [ht2f _ (by omega)]
    exact memory_inverse hT (by omega) node t1 ht1m i hi
  have hu2e : ∀ i, i<q*q → u2.memory (E+i)=some (conversionTable (p^(e+1)) q node i) ∧ conversionTable (p^(e+1)) q node i<p^(e+1) :=
    memory_conversion hT (by omega) node t2 ht2m
  have hu2x : ∀ i, i<A*q^d → u2.memory (S+i)=some (x i) ∧ x i<p^(e+1) := by
    intro i hi
    change t2.memory _=_ ∧ _
    rw [ht2f _ (by omega)]
    change t1.memory _=_ ∧ _
    rw [ht1f _ (by omega)]
    exact hx i hi
  obtain ⟨c3,z,ez,hc3,hzr,hzm,hzf⟩:=command_correct u2 x (inverseTable (p^(e+1)) q node) (conversionTable (p^(e+1)) q node)
    hk hkw hq hA hT hadd hmul hL hLw hP hS hC hE hD hPS hCP hCS hEP hES hu2r hu2ctx hu2x hu2c hu2e
  refine ⟨4+(c1+(4+(c2+(8+c3)))),z,Eval.seq eu (Eval.seq et1 (Eval.seq eu1 (Eval.seq et2 (Eval.seq eu2 ez)))),by omega,hzr,?_,?_⟩
  · intro i hi
    exact (hzm i hi).1
  · intro a haP haS haC haE
    rw [hzf a haP haS]
    change t2.memory a=s.memory a
    rw [ht2f a haE]
    exact ht1f a haC
end
end DeterministicThreeSum.Structured.Indexed.NewtonPass

end OAI
