import Mathlib
import OAI.Computability.MinUncut.Search.RationalInner

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian
abbrev InnerDataRaw := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ × ℚ
def innerDataEquiv : InnerData ≃ InnerDataRaw where
  toFun d := (d.s,d.m,d.k,d.n,d.H,d.A,d.γ,d.p,d.θ)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2.1,x.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance innerDataPrimcodable : Primcodable InnerData := Primcodable.ofEquiv InnerDataRaw innerDataEquiv
@[fun_prop] lemma c_innerData_s : Computable (InnerData.s) :=
  (Primrec.fst.comp (Primrec.of_equiv (e:=innerDataEquiv))).to_comp
@[fun_prop] lemma c_innerData_m : Computable (InnerData.m) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))).to_comp
@[fun_prop] lemma c_innerData_k : Computable (InnerData.k) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv))))).to_comp
@[fun_prop] lemma c_innerData_n : Computable (InnerData.n) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))))).to_comp
@[fun_prop] lemma c_innerData_H : Computable (InnerData.H) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv))))))).to_comp
@[fun_prop] lemma c_innerData_A : Computable (InnerData.A) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))))))).to_comp
@[fun_prop] lemma c_innerData_γ : Computable (InnerData.γ) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv))))))))).to_comp
@[fun_prop] lemma c_innerData_p : Computable (InnerData.p) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))))))))).to_comp
@[fun_prop] lemma c_innerData_θ : Computable (InnerData.θ) :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))))))))).to_comp
abbrev OuterDataRaw := ℚ × ℚ × ℚ × ℕ × ℕ
def outerDataEquiv : OuterData ≃ OuterDataRaw where
  toFun d := (d.u,d.b4,d.v,d.k,d.t)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance outerDataPrimcodable : Primcodable OuterData := Primcodable.ofEquiv OuterDataRaw outerDataEquiv
@[fun_prop] lemma c_outerData_u : Computable (OuterData.u) :=
  (Primrec.fst.comp (Primrec.of_equiv (e:=outerDataEquiv))).to_comp
@[fun_prop] lemma c_outerData_b4 : Computable (OuterData.b4) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e:=outerDataEquiv)))).to_comp
@[fun_prop] lemma c_outerData_v : Computable (OuterData.v) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=outerDataEquiv))))).to_comp
@[fun_prop] lemma c_outerData_k : Computable (OuterData.k) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=outerDataEquiv)))))).to_comp
@[fun_prop] lemma c_outerData_t : Computable (OuterData.t) :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=outerDataEquiv)))))).to_comp
abbrev GridDataRaw := ℕ × ℕ × ℕ
def gridDataEquiv : GridData ≃ GridDataRaw where
  toFun d := (d.T,d.L,d.r)
  invFun x := ⟨x.1,x.2.1,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance gridDataPrimcodable : Primcodable GridData := Primcodable.ofEquiv GridDataRaw gridDataEquiv
@[fun_prop] lemma c_gridData_T : Computable (GridData.T) :=
  (Primrec.fst.comp (Primrec.of_equiv (e:=gridDataEquiv))).to_comp
@[fun_prop] lemma c_gridData_L : Computable (GridData.L) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e:=gridDataEquiv)))).to_comp
@[fun_prop] lemma c_gridData_r : Computable (GridData.r) :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=gridDataEquiv)))).to_comp

@[fun_prop] lemma c_sigma : Computable rationalSigma := by unfold rationalSigma; fun_prop
@[fun_prop] lemma c_eta : Computable rationalEta := by unfold rationalEta; fun_prop
@[fun_prop] lemma c_R : Computable rationalR := by unfold rationalR; fun_prop
@[fun_prop] lemma c_T : Computable rationalT := by unfold rationalT; fun_prop
end MinUncut.Preprocess

end

end OAI
