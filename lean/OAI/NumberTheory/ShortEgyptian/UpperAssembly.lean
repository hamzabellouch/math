import OAI.NumberTheory.ShortEgyptian.DenseSplit

namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

lemma dense_remainder (S : ℝ) (hS : 0<S) (hX : 4<Real.exp ((dimX:ℝ)*S))
    (C : ℕ) (hC : 0<C) (D : DenseData S C) (A : ℕ) (hA : 0<A)
    (hAb : (A:ℝ)≤Real.exp S) :
    ∃ ns, IsUnitSum ((A:ℚ)/C) ns ∧ (ns.length:ℝ)≤2*densityConstant*Real.log S := by
  let X := Real.exp ((dimX:ℝ)*S)
  let P := A*D.M
  have hM : 0<D.M := by exact_mod_cast (Real.exp_pos S).trans D.M_lower
  have hP : 0<P := Nat.mul_pos hA hM
  have hPX : (P:ℝ)≤X := by
    calc
      (P:ℝ) = (A:ℝ)*(D.M:ℝ) := by simp only [P,Nat.cast_mul]
      _ ≤ Real.exp S*Real.exp ((dimM:ℝ)*S) := mul_le_mul hAb D.M_upper (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((1+(dimM:ℝ))*S) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ X := by
        apply Real.exp_le_exp.mpr
        have heq : (dimX:ℝ) = (dimM:ℝ)+2 := by norm_num [dimX]
        rw [heq]
        nlinarith
  let g := ⌊X/(P:ℝ)⌋₊
  let n := g*P
  have hf := floor_multiple X P hP hPX
  change 0<g ∧ X/2≤(n:ℝ) ∧ (n:ℝ)≤X at hf
  obtain ⟨u,hu,v,hv,hn⟩ := dense_split X hX D.G n hf.2.1 hf.2.2 D.bad_card
  obtain ⟨xs,hxs,hxlen⟩ := D.expansion u hu
  obtain ⟨ys,hys,hylen⟩ := D.expansion v hv
  have hh := isUnitSum_scale (isUnitSum_append hxs hys) g hf.1
  have hMn : (D.M:ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hCn : (C:ℚ) ≠ 0 := by exact_mod_cast hC.ne'
  have hgn : (g:ℚ) ≠ 0 := by exact_mod_cast hf.1.ne'
  have hnQ : (u:ℚ)+v=(g:ℚ)*(A*D.M) := by
    have hh : u+v=g*(A*D.M) := hn.symm
    exact_mod_cast hh
  have heq : ((u:ℚ)/(D.M*C)+(v:ℚ)/(D.M*C))/(g:ℚ)=(A:ℚ)/C := by
    rw [←add_div,hnQ]
    field_simp
  rw [heq] at hh
  refine ⟨(xs++ys).map (g*·),hh,?_⟩
  simp only [List.length_map,List.length_append,Nat.cast_add]
  linarith

noncomputable def upperConstant : ℝ := greedyConstant+2*densityConstant

lemma upperConstant_pos : 0<upperConstant := by
  dsimp [upperConstant]
  linarith [greedyConstant_pos,densityConstant_pos]

lemma upper_at_scale (S : ℝ) (hS : 2≤S) (hlog : 1≤Real.log S)
    (hdens : ∀ C : ℕ, Real.exp ((dimC:ℝ)*S)≤C → (C:ℝ)≤Real.exp (2*(dimC:ℝ)*S) → Nonempty (DenseData S C))
    (a b : ℕ) (ha : 0<a) (hab : a<b) (hb : (b:ℝ)=Real.exp S) :
    ∃ ns, IsExpansion a b ns ∧ (ns.length:ℝ)≤upperConstant*Real.log S := by
  have hSp : 0<S := by linarith
  have hDC : (1:ℝ)<dimC := by norm_num [dimC,dimX,dimM]
  have hDX : (1:ℝ)<dimX := by norm_num [dimX,dimM]
  let T := Real.exp ((dimC:ℝ)*S)
  have hT : 1<T := Real.one_lt_exp_iff.mpr (by nlinarith)
  have hbT : (b:ℝ)<T := by rw [hb]; apply Real.exp_lt_exp.mpr; nlinarith
  obtain ⟨xs,A,C,hxs,hxlen,hAa,hAC,heq,hstop⟩ := prepare_denominator a b ha hab T hT hbT
    (greedySteps S) (greedy_power_cap S hSp)
  have hxlenR : (xs.length:ℝ) ≤ greedyConstant*Real.log S :=
    (Nat.cast_le.mpr hxlen).trans (greedy_length_bound S (by linarith) hlog)
  have hlog0 : 0≤Real.log S := by linarith
  have hex : ∃ ns, IsUnitSum ((a:ℚ)/b) ns ∧ (ns.length:ℝ)≤upperConstant*Real.log S := by
    rcases hstop with hA0 | hCbound
    · refine ⟨xs,⟨hxs,?_⟩,?_⟩
      · simpa only [hA0,Nat.cast_zero,zero_div,add_zero] using heq.symm
      · dsimp [upperConstant]
        nlinarith [mul_nonneg densityConstant_pos.le hlog0]
    · have hChi : (C:ℝ)≤Real.exp (2*(dimC:ℝ)*S) := by
        apply hCbound.2.le.trans_eq
        dsimp [T]
        rw [pow_two,←Real.exp_add]
        congr 1
        ring
      obtain ⟨D⟩ := hdens C hCbound.1 hChi
      by_cases hA0 : A=0
      · refine ⟨xs,⟨hxs,?_⟩,?_⟩
        · simpa only [hA0,Nat.cast_zero,zero_div,add_zero] using heq.symm
        · dsimp [upperConstant]
          nlinarith [mul_nonneg densityConstant_pos.le hlog0]
      have hAp : 0<A := Nat.pos_of_ne_zero hA0
      have hC : 0<C := hAp.trans hAC
      have hX : 4<Real.exp ((dimX:ℝ)*S) := by
        have hadd := Real.add_one_le_exp ((dimX:ℝ)*S)
        have hD : (3:ℝ)≤dimX := by norm_num [dimX,dimM]
        nlinarith
      have hAb : (A:ℝ) ≤ Real.exp S := by rw [←hb]; exact_mod_cast hAa.trans hab.le
      obtain ⟨ys,hys,hylen⟩ := dense_remainder S hSp hX C hC D A hAp hAb
      refine ⟨xs++ys,⟨?_,?_⟩,?_⟩
      · intro n hn
        rcases List.mem_append.mp hn with hn | hn
        · exact hxs n hn
        · exact hys.1 n hn
      · rw [unitSum_append,hys.2]
        exact heq.symm
      · dsimp [upperConstant]
        simp only [List.length_append,Nat.cast_add]
        nlinarith
  obtain ⟨ns,hns,hlen⟩ := hex
  obtain ⟨ys,hys,hylen⟩ := remove_repetitions ha hab ns (fun n hn => by have := hns.1 n hn; omega) hns.2
  exact ⟨ys,hys,by simpa only [hylen] using hlen⟩

end ShortEgyptian

end OAI
