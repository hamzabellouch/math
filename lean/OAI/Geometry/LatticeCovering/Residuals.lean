import OAI.Geometry.LatticeCovering.Products

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

lemma suffixBinary_fixed {m n : ℕ} (P : Finset (Fin m → ℝ)) (t : Fin n → ℝ)
    (hP : SuffixBinary P) : SuffixBinary (P.image (fun v => Fin.append v t)) := by
  classical
  intro j y
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · obtain ⟨a,ha⟩ := hP j (fun k => y (Fin.castAdd n k))
    refine ⟨a,?_⟩
    intro l hl hly
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
    simpa only [Fin.append_left] using ha v hv (fun k hk => by
      simpa only [Fin.append_left] using hly (Fin.castAdd n k) hk)
  · refine ⟨t j,?_⟩
    intro l hl hly
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
    simp only [Fin.append_right,true_or]

lemma gamma_unit_box {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) :
    gamma1 1^n ≤ gamma x := by
  have hl (j : Fin n) : gamma1 1 ≤ gamma1 (x j) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    have hj := (sq_le_one_iff_abs_le_one (x j)).mpr (hx j)
    norm_num
    nlinarith
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => (gamma1_pos 1).le) (fun j _ => hl j)
  simpa only [gamma,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hprod

namespace Chain
variable {B : Block}

def FullResidual (c : Chain B) (y l : c.FullVec) : Prop :=
  c.Residual (c.subLast (fun j => y (Fin.castAdd B.terminalDim j))
    (B.terminalShift (fun j => l (Fin.natAdd c.dim j))))
    (fun j => l (Fin.castAdd B.terminalDim j)) ∧
  ∀ j, |y (Fin.natAdd c.dim j)-l (Fin.natAdd c.dim j)| ≤ 1

def FullSelected (c : Chain B) (y l : c.FullVec) : Prop :=
  c.Selected (c.subLast (fun j => y (Fin.castAdd B.terminalDim j))
    (B.terminalShift (fun j => l (Fin.natAdd c.dim j))))
    (fun j => l (Fin.castAdd B.terminalDim j))




theorem full_patterns (c : Chain B) (loss : Block → ℝ) (hc : c.Good loss)
    (hmean : (1 : ℝ)/2 ≤ (𝔼 z, B.g z)) (y : c.FullVec) :
    ∃ P : Finset c.FullVec, SuffixBinary P ∧
      (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧ c.FullSelected y l) ∧
      (∃ t : Fin B.terminalDim → ℝ, ∀ l ∈ P, ∀ j, l (Fin.natAdd c.dim j)=t j) ∧
      c.coefficient loss*(1/2)*gamma1 1^B.terminalDim ≤
        ∑ l ∈ P, c.det*gamma (y-c.fullLinear l) := by
  classical
  obtain ⟨z,hz,hgz⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  let yl : c.Vec := fun j => y (Fin.castAdd B.terminalDim j)
  let yr : Fin B.terminalDim → ℝ := fun j => y (Fin.natAdd c.dim j)
  obtain ⟨t,ht,htr,htg⟩ := B.terminal_index (c.last yl) yr z
  let y' := c.subLast yl (B.terminalShift t)
  obtain ⟨P,hPb,hPm,hPw⟩ := c.truncated_patterns_selected loss hc y'
  have hg' : B.g (B.grid (c.last y'))=B.g z := by
    rw [last_subLast,htg]
  have hPw' : c.coefficient loss*(1/2) ≤ ∑ l ∈ P, c.weight y' l := by
    rw [hg'] at hPw
    exact (mul_le_mul_of_nonneg_left hgz (c.coefficient_nonneg loss hc)).trans hPw
  refine ⟨P.image (fun v => Fin.append v t),suffixBinary_fixed P t hPb,?_,⟨t,?_⟩,?_⟩
  · intro l hl
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
    have hv' := hPm v hv
    refine ⟨?_,?_,?_⟩
    · change (Fin.append v t) ∈ finProduct c.rawLattice (integerLattice B.terminalDim)
      simp only [mem_finProduct,Fin.append_left,Fin.append_right]
      exact ⟨(c.mem_raw v).mpr hv'.1,ht⟩
    · simpa only [FullResidual,Fin.append_left,Fin.append_right] using And.intro hv'.2.1 htr
    · simpa only [FullSelected,Fin.append_left,Fin.append_right] using hv'.2.2
  · intro l hl j
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hl
    simp only [Fin.append_right]
  · rw [Finset.sum_image]
    · simp only [full_weight]
      rw [←Finset.sum_mul]
      apply mul_le_mul hPw' (gamma_unit_box (yr-t) htr)
        (pow_nonneg (gamma1_pos 1).le _)
        ((mul_nonneg (c.coefficient_nonneg loss hc) (by norm_num)).trans hPw')
    · intro v hv w hw he
      funext j
      simpa only [Fin.append_left] using congrFun he (Fin.castAdd B.terminalDim j)


end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

lemma gamma_le_one {n : ℕ} (x : Fin n → ℝ) : gamma x ≤ 1 := by
  apply Finset.prod_le_one₀ (fun j _ => (gamma1_pos _).le)
  intro j _
  have hs : (1 : ℝ) ≤ Real.sqrt (2*Real.pi) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2*Real.pi by positivity)
    nlinarith [Real.pi_gt_three,Real.sqrt_nonneg (2*Real.pi)]
  have he : Real.exp (-((x j)^2)/2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x j)])
  exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs)).mpr (by simpa using he.trans hs)

namespace Chain
variable {A B : Block}

lemma dim_last_le (c : Chain B) (hc : c.Halving) : c.dim+B.b ≤ 2*c.first.b := by
  induction c with
  | base B => simp [dim,first, two_mul]
  | @append A c B w ih =>
    have ht := ih hc.1
    change c.dim+B.b+B.b ≤ 2*c.first.b
    have hh := hc.2
    omega
lemma last_le_first (c : Chain B) (hc : c.Halving) : B.b ≤ c.first.b := by
  induction c with
  | base B => exact le_refl _
  | @append A c B w ih =>
    have ht := ih hc.1
    change B.b ≤ c.first.b
    have hh := hc.2
    omega
lemma every_le_first (c : Chain B) (hc : c.Halving) : c.Every (fun Q => Q.b ≤ c.first.b) := by
  induction c with
  | base B => exact le_refl _
  | @append A c B w ih =>
    exact ⟨ih hc.1,last_le_first (.append c B w) hc⟩

lemma blockSum_dim (c : Chain B) : c.blockSum (fun Q => (Q.b : ℝ)) = (c.dim : ℝ) := by
  induction c with
  | base B => rfl
  | append c B w ih => simp only [blockSum,dim,ih,Nat.cast_add]

def heights : {B : Block} → (c : Chain B) → c.Vec
  | _, .base B => fun _ => B.h
  | _, .append c B _ => Fin.append c.heights (fun _ => B.h)

def radiusSq (c : Chain B) : ℝ := c.blockSum (fun Q => (Q.b : ℝ)*Q.h^2)

lemma heights_square_sum (c : Chain B) : ∑ j, c.heights j^2 = c.radiusSq := by
  induction c with
  | base B => simp [heights,radiusSq,blockSum]
  | append c B w ih =>
    simp only [heights,Fin.sum_univ_add,Fin.append_left,Fin.append_right,ih,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rfl

lemma residual_physical (c : Chain B) (y l : c.Vec) (hl : c.Residual y l) :
    ∀ j, |(y-c.linear l) j| ≤ c.heights j := by
  induction c with
  | base B => exact hl
  | @append A c B w ih =>
    rw [residual_append]
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [heights,Fin.append_left] using ih _ _ hl.1 k
    · simpa only [heights,Fin.append_right] using hl.2 k

lemma heights_nonneg (c : Chain B) : ∀ j, 0 ≤ c.heights j := by
  induction c with
  | base B => exact fun _ => B.h_pos.le
  | append c B w ih =>
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [heights,Fin.append_left] using ih k
    · simpa only [heights,Fin.append_right] using B.h_pos.le

lemma full_residual_square (c : Chain B) (y l : c.FullVec) (hl : c.FullResidual y l) :
    (∑ j, ((y-c.fullLinear l) j)^2) ≤ c.radiusSq+(B.terminalDim : ℝ) := by
  have he : l=Fin.append (fun j => l (Fin.castAdd B.terminalDim j))
      (fun j => l (Fin.natAdd c.dim j)) := by
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp
  rw [he,full_residual,Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right]
  have hp := c.residual_physical _ _ hl.1
  have hsum : (∑ j, ((c.subLast (fun j => y (Fin.castAdd B.terminalDim j))
      (B.terminalShift (fun j => l (Fin.natAdd c.dim j))) -
      c.linear (fun j => l (Fin.castAdd B.terminalDim j))) j)^2) ≤ c.radiusSq := by
    rw [←heights_square_sum]
    apply Finset.sum_le_sum
    intro j _
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (c.heights_nonneg j)).2 (hp j)
  have ht : (∑ j, (y (Fin.natAdd c.dim j)-l (Fin.natAdd c.dim j))^2) ≤ (B.terminalDim : ℝ) := by
    calc
      _ ≤ ∑ j : Fin B.terminalDim, (1 : ℝ) := Finset.sum_le_sum (fun j _ =>
        (sq_le_one_iff_abs_le_one _).mpr (hl.2 j))
      _ = _ := by simp
  exact add_le_add hsum ht

def AtomBound (q : Block → ℝ) (B : Block) : Prop :=
  ∀ z ∈ B.usable, ∀ t : B.Vec, t ∈ gridCell B.p z →
    ∀ e : Fin B.b → Bool, atom B.h t e/(B.p : ℝ) ≤ q B

lemma selected_cap (c : Chain B) (k : ℝ) (hk : 0 ≤ k)
    (hc : c.Every (AtomBound (fun Q => Real.exp (-k*(Q.b : ℝ)^(70/100 : ℝ)))))
    (y l : c.Vec) (hl : c.Selected y l) :
    c.weight y l ≤ Real.exp (-k*(c.first.b : ℝ)^(70/100 : ℝ)) := by
  induction c with
  | base B => exact B.selected_weight_le y l hl _ hc
  | @append A c B w ih =>
    have hp := ih hc.1 _ _ hl.1
    have hb := B.selected_weight_le _ _ hl.2 _ hc.2
    have he : Real.exp (-k*(B.b : ℝ)^(70/100 : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    change c.weight _ _*B.weight _ _ ≤ _
    exact (mul_le_mul_of_nonneg_left (hb.trans he) (c.weight_pos _ _).le).trans
      (by simpa only [mul_one,first] using hp)

lemma full_selected_cap (c : Chain B) (k : ℝ) (hk : 0 ≤ k)
    (hc : c.Every (AtomBound (fun Q => Real.exp (-k*(Q.b : ℝ)^(70/100 : ℝ)))))
    (y l : c.FullVec) (hl : c.FullSelected y l) :
    c.det*gamma (y-c.fullLinear l) ≤ Real.exp (-k*(c.first.b : ℝ)^(70/100 : ℝ)) := by
  have he : l=Fin.append (fun j => l (Fin.castAdd B.terminalDim j))
      (fun j => l (Fin.natAdd c.dim j)) := by
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp
  rw [he,full_weight]
  exact (mul_le_mul_of_nonneg_left (gamma_le_one _) (c.weight_pos _ _).le).trans
    (by simpa only [mul_one] using c.selected_cap k hk hc _ _ hl)



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Filter Topology
open scoped BigOperators

lemma gamma1_le_one (x : ℝ) : gamma1 x ≤ 1 := by
  have h := gamma_le_one (fun _ : Fin 1 => x)
  simpa only [gamma,Fin.prod_univ_one] using h

namespace Chain
variable {B : Block}

lemma blockSum_add (c : Chain B) (f g : Block → ℝ) :
    c.blockSum (fun Q => f Q+g Q) = c.blockSum f+c.blockSum g := by
  induction c with
  | base B => rfl
  | append c B w ih => simp only [blockSum,ih]; ring

lemma radius_bound (c : Chain B) (A : ℝ)
    (hc : c.Halving) (hr : c.Every (Regular A))
    (hp : c.Every (fun Q => 1 ≤ Q.b)) :
    c.radiusSq ≤ (9/2 : ℝ)*(c.first.b : ℝ)*Real.log ((c.first.b : ℝ)+1) := by
  have hf : 0 < (c.first.b : ℝ)+1 := by positivity
  have hlog : 0 ≤ Real.log ((c.first.b : ℝ)+1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg c.first.b : (0 : ℝ) ≤ c.first.b)])
  have hle := c.every_le_first hc
  have he : c.Every (fun Q => (Q.b : ℝ)*Q.h^2 ≤
      ((9/4 : ℝ)*Real.log ((c.first.b : ℝ)+1))*(Q.b : ℝ)) := by
    have hm : ∀ {Q : Block} (d : Chain Q), d.Every (Regular A) →
        d.Every (fun Q => 1 ≤ Q.b) → d.Every (fun Q => Q.b ≤ c.first.b) →
        d.Every (fun Q => (Q.b : ℝ)*Q.h^2 ≤
          ((9/4 : ℝ)*Real.log ((c.first.b : ℝ)+1))*(Q.b : ℝ)) := by
      intro Q d
      induction d with
      | base Q =>
        intro hQ hpQ hlQ
        change 1 ≤ Q.b at hpQ
        change Q.b ≤ c.first.b at hlQ
        change (Q.b : ℝ)*Q.h^2 ≤ _
        rw [hQ.1]
        change (Q.b : ℝ)*heightR (Q.b : ℝ)^2 ≤ _
        rw [heightR_sq (by exact_mod_cast hpQ)]
        have hql : Real.log (Q.b : ℝ) ≤ Real.log ((c.first.b : ℝ)+1) :=
          Real.log_le_log (by exact_mod_cast (show 0 < Q.b by omega))
            (by
              have hcast : (Q.b : ℝ) ≤ c.first.b := by exact_mod_cast hlQ
              linarith)
        nlinarith [mul_le_mul_of_nonneg_left hql (Nat.cast_nonneg Q.b)]
      | append d Q w ih =>
        intro hr hp hl
        refine ⟨ih hr.1 hp.1 hl.1,?_⟩
        change (Q.b : ℝ)*Q.h^2 ≤ _
        rw [hr.2.1]
        change (Q.b : ℝ)*heightR (Q.b : ℝ)^2 ≤ _
        rw [heightR_sq (by exact_mod_cast hp.2)]
        have hql : Real.log (Q.b : ℝ) ≤ Real.log ((c.first.b : ℝ)+1) :=
          Real.log_le_log (by exact_mod_cast (show 0 < Q.b by have := hp.2; omega))
            (by
              have hcast : (Q.b : ℝ) ≤ c.first.b := by exact_mod_cast hl.2
              linarith)
        nlinarith [mul_le_mul_of_nonneg_left hql (Nat.cast_nonneg Q.b)]
    exact hm c hr hp hle
  calc
    c.radiusSq ≤ c.blockSum (fun Q => ((9/4 : ℝ)*Real.log ((c.first.b : ℝ)+1))*(Q.b : ℝ)) :=
      c.blockSum_le _ _ he
    _ = ((9/4 : ℝ)*Real.log ((c.first.b : ℝ)+1))*(c.dim : ℝ) := by
      rw [blockSum_mul,blockSum_dim]
    _ ≤ (9/2 : ℝ)*(c.first.b : ℝ)*Real.log ((c.first.b : ℝ)+1) := by
      have hd : (c.dim : ℝ) ≤ 2*(c.first.b : ℝ) := by
        exact_mod_cast (show c.dim ≤ 2*c.first.b by have := c.dim_last_le hc; omega)
      nlinarith [mul_le_mul_of_nonneg_left hd hlog]

lemma coefficient_half (c : Chain B) (A : ℝ) (hA : 0 ≤ A) (cutoff : ℕ)
    (hcut : 1 ≤ cutoff) (hc : c.Halving)
    (hr : c.Every (fun Q => cutoff ≤ Q.b ∧
      Q.roundingLoss ≤ (Q.b : ℝ)^(-(1/100 : ℝ)) ∧ blockLoss A Q ≤ 1/2))
    (hsmall : (1+2*A)*(cutoff : ℝ)^(-(1/100 : ℝ))/(1-(2 : ℝ)^(-(1/100 : ℝ))) ≤ 1/2) :
    1/2 ≤ c.coefficient (blockLoss A) := by
  have hl := c.every_mono hr (fun Q hQ => show blockLoss A Q ∈ Set.Icc (0 : ℝ) 1 from
    ⟨mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _),hQ.2.2.trans (by norm_num)⟩)
  obtain ⟨h0,h1,hd⟩ := c.coefficient_bounds (blockLoss A) hl
  have hsum := c.inverse_power_sum (1/100 : ℝ) (by norm_num) hc
    (c.every_mono hr (fun Q hQ => by omega))
  have hd0 : 0 < 1-(2 : ℝ)^(-(1/100 : ℝ)) := by
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hlast : (B.b : ℝ)^(-(1/100 : ℝ)) ≤ (cutoff : ℝ)^(-(1/100 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < cutoff by omega))
      (by exact_mod_cast (c.every_last hr).1) (by norm_num)
  have hsum' : c.blockSum (fun Q => Q.roundingLoss+2*blockLoss A Q) ≤
      (1+2*A)*c.blockSum (fun Q => (Q.b : ℝ)^(-(1/100 : ℝ))) := by
    rw [←blockSum_mul]
    apply c.blockSum_le
    exact c.every_mono hr (fun Q hQ => by dsimp [blockLoss]; nlinarith [hQ.2.1])
  have hb0 : 0 ≤ blockLoss A B := (c.every_last hl).1
  have hbound : (1+2*A)*c.blockSum (fun Q => (Q.b : ℝ)^(-(1/100 : ℝ))) ≤ 1/2 := by
    calc
      _ ≤ (1+2*A)*((B.b : ℝ)^(-(1/100 : ℝ))/(1-(2 : ℝ)^(-(1/100 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (1+2*A)*((cutoff : ℝ)^(-(1/100 : ℝ))/(1-(2 : ℝ)^(-(1/100 : ℝ)))) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlast hd0.le) (by positivity)
      _ ≤ _ := by simpa only [mul_div_assoc] using hsmall
  linarith

lemma terminal_bound (c : Chain B) (A : ℝ) {cutoff M Q : ℕ}
    (hr : Regular A B) (hstop : nextSize B.b < cutoff)
    (hM : (cutoff : ℝ)^((1 : ℝ)/(9/10)) ≤ M)
    (hQ : Real.exp ((M : ℝ)^2) ≤ Q)
    (hlog : logMean (height B.b) ≤ (B.b : ℝ)) :
    B.b ≤ M ∧ B.p ≤ Q ∧ B.terminalDim ≤ M*Nat.clog 2 Q := by
  have _ := c
  have hb : (B.b : ℝ) ≤ M := by
    exact (nextSize_relation B.b).trans ((Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast hstop.le) (by norm_num : (0 : ℝ) ≤ 1/(9/10))).trans hM)
  have hb' : B.b ≤ M := by exact_mod_cast hb
  have hp : Real.log B.p ≤ (M : ℝ)^2 := by
    have hs : 0 ≤ (B.b : ℝ)^(56/100 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg B.b)
    have hb2 := pow_le_pow_left₀ (Nat.cast_nonneg B.b) hb 2
    nlinarith [hr.2.2.1]
  have hp' : B.p ≤ Q := by
    have hexp := (Real.exp_le_exp.mpr hp).trans hQ
    rw [Real.exp_log (by exact_mod_cast B.prime.pos)] at hexp
    exact_mod_cast hexp
  exact ⟨hb',hp',Nat.mul_le_mul hb' (Nat.clog_mono_right 2 hp')⟩

end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Filter Topology
open scoped BigOperators




theorem vertical_patterns_core :
    ∃ cutoff : ℕ, 2 ≤ cutoff ∧ ∃ C k κ : ℝ, 0 < C ∧ 0 < k ∧ 0 < κ ∧
      ∀ b₁ ≥ cutoff, ∃ B : Block, ∃ c : Chain B,
        c.first.b=b₁ ∧ c.CeilingSizes ∧
        (c.dim+B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)+1) ∧
        c.radiusSq+(B.terminalDim : ℝ) ≤ C*((b₁ : ℝ)*Real.log ((b₁ : ℝ)+1)+1) ∧
        ∀ y : c.FullVec, ∃ P : Finset c.FullVec,
          P.Nonempty ∧ SuffixBinary P ∧
          (∀ l ∈ P, l ∈ c.fullRaw ∧ c.FullResidual y l ∧
            c.det*gamma (y-c.fullLinear l) ≤ Real.exp (-k*(b₁ : ℝ)^(70/100 : ℝ))) ∧
          (∃ t : Fin B.terminalDim → ℝ, ∀ l ∈ P, ∀ j, l (Fin.natAdd c.dim j)=t j) ∧
          κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l) := by
  classical
  obtain ⟨A,hA,N,hN,hsmall,hbuild⟩ := hierarchy_preparation
  obtain ⟨k,hk,hatom⟩ := eventually_eligible_atom
  have hround : ∀ᶠ b : ℕ in atTop, ∀ p : ℕ, 0 < p →
      (b : ℝ)*logMean (height b)-4*(b : ℝ)^(56/100 : ℝ) ≤ Real.log p →
      (b : ℝ)*height b^2/p ≤ (b : ℝ)^(-(1/100 : ℝ)) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually eventually_rounding_slack,
      eventually_ge_atTop (1 : ℕ)] with b hb hb1 p hp hpl
    exact (hb p (by exact_mod_cast hp) hpl).1.trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hb1) (by norm_num))
  have hden : 0 < 1-(2 : ℝ)^(-(1/100 : ℝ)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  have hsumSmall : ∀ᶠ b : ℕ in atTop,
      (1+2*A)*(b : ℝ)^(-(1/100 : ℝ))/(1-(2 : ℝ)^(-(1/100 : ℝ))) ≤ 1/2 := by
    have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/100)).const_mul (1+2*A)).div_const
      (1-(2 : ℝ)^(-(1/100 : ℝ)))
    have hn : Tendsto (fun b : ℕ => (1+2*A)*(b : ℝ)^(-(1/100 : ℝ))/
        (1-(2 : ℝ)^(-(1/100 : ℝ)))) atTop (𝓝 0) := by
      have hcast : Tendsto (fun b : ℕ => (b : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def,mul_zero,zero_div] using ht.comp hcast
    exact hn.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨N',hN'⟩ := eventually_atTop.mp (hatom.and (hround.and hsumSmall))
  let cutoff := max N N'
  have hcutN : N ≤ cutoff := le_max_left _ _
  have hcutN' : N' ≤ cutoff := le_max_right _ _
  have hcut2 : 2 ≤ cutoff := hN.trans hcutN
  let M : ℕ := ⌈(cutoff : ℝ)^((1 : ℝ)/(9/10))⌉₊
  let Q : ℕ := ⌈Real.exp ((M : ℝ)^2)⌉₊
  let T : ℕ := M*Nat.clog 2 Q
  let C : ℝ := (T : ℝ)+5
  let κ : ℝ := (1/4 : ℝ)*gamma1 1^T
  have hκ : 0 < κ := mul_pos (by norm_num) (pow_pos (gamma1_pos 1) _)
  refine ⟨cutoff,hcut2,C,k,κ,by dsimp [C]; positivity,hk,hκ,?_⟩
  intro b₁ hb₁
  obtain ⟨B,c,hfirst,hreg,hgood,hhalf,hsizes,hstop⟩ := hbuild cutoff hcutN b₁ hb₁
  have hbN (W : Block) (hW : cutoff ≤ W.b) := hsmall W.b (hcutN.trans hW)
  have hbN' (W : Block) (hW : cutoff ≤ W.b) := hN' W.b (hcutN'.trans hW)
  have hr := c.every_mono hreg (fun W hW => hW.2)
  have hpos := c.every_mono hreg (fun W hW => show 1 ≤ W.b by omega)
  have hB := c.every_last hreg
  have hBound := c.terminal_bound A hB.2 hstop (Nat.le_ceil _) (Nat.le_ceil _) (hbN B hB.1).2
  have hT : B.terminalDim ≤ T := hBound.2.2
  have hloss : c.Every (fun W => cutoff ≤ W.b ∧
      W.roundingLoss ≤ (W.b : ℝ)^(-(1/100 : ℝ)) ∧ blockLoss A W ≤ 1/2) := by
    apply c.every_mono hreg
    intro W hW
    refine ⟨hW.1,?_,(hbN W hW.1).1⟩
    dsimp [Block.roundingLoss]
    rw [hW.2.1]
    exact (hbN' W hW.1).2.1 W.p W.prime.pos hW.2.2.1
  have hcoeff : 1/2 ≤ c.coefficient (blockLoss A) :=
    c.coefficient_half A hA.le cutoff (by omega) hhalf hloss (hN' cutoff hcutN').2.2
  have hcAtoms : c.Every (Chain.AtomBound (fun W => Real.exp (-k*(W.b : ℝ)^(70/100 : ℝ)))) := by
    apply c.every_mono hreg
    intro W hW z hz t ht e
    rw [hW.2.1]
    exact ((hbN' W hW.1).1 W.p hW.2.2.1 z (hW.2.2.2.2.1 hz) t ht e).2
  refine ⟨B,c,hfirst,hsizes,?_,?_,?_⟩
  · have hd : (c.dim : ℝ) ≤ 2*(b₁ : ℝ) := by
      exact_mod_cast (show c.dim ≤ 2*b₁ by have := c.dim_last_le hhalf; omega)
    have ht : (B.terminalDim : ℝ) ≤ T := by exact_mod_cast hT
    dsimp [C]
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T),(Nat.cast_nonneg b₁ : (0 : ℝ) ≤ b₁),
      mul_nonneg (show (0 : ℝ) ≤ T by positivity) (show (0 : ℝ) ≤ b₁ by positivity)]
  · have hradius := c.radius_bound A hhalf hr hpos
    rw [hfirst] at hradius
    have ht : (B.terminalDim : ℝ) ≤ T := by exact_mod_cast hT
    have hlog : 0 ≤ Real.log ((b₁ : ℝ)+1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg b₁ : (0 : ℝ) ≤ b₁)])
    dsimp [C]
    nlinarith [mul_nonneg (Nat.cast_nonneg b₁) hlog,
      mul_nonneg (Nat.cast_nonneg T) (mul_nonneg (Nat.cast_nonneg b₁) hlog)]
  · intro y
    obtain ⟨P,hPb,hPl,hPt,hPw⟩ := c.full_patterns (blockLoss A) hgood
      (regular_mean hB.2 (hbN B hB.1).1).1 y
    have hgT : gamma1 1^T ≤ gamma1 1^B.terminalDim :=
      pow_le_pow_of_le_one (gamma1_pos 1).le (gamma1_le_one 1) hT
    have hweight : κ ≤ ∑ l ∈ P, c.det*gamma (y-c.fullLinear l) := by
      apply le_trans _ hPw
      dsimp [κ]
      have h0 : 0 ≤ gamma1 1^B.terminalDim := (pow_pos (gamma1_pos 1) _).le
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) h0]
    have hPn : P.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at hweight
      exact (not_le_of_gt hκ) hweight
    refine ⟨P,hPn,hPb,?_,hPt,hweight⟩
    intro l hl
    have hle := hPl l hl
    refine ⟨hle.1,hle.2.1,?_⟩
    have hcap := c.full_selected_cap k hk.le hcAtoms y l hle.2.2
    simpa only [hfirst] using hcap


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry
open scoped BigOperators

namespace Block
lemma shiftDim_bound (B : Block) (d : ℕ) (w : Fin d → B.Group) (l : Fin d → ℝ)
    {S : ℝ} (hS : 0 ≤ S) (hl : ∀ j, |l j| ≤ S) (j : Fin B.b) :
    |B.shiftDim d w l j| ≤ B.h*((d : ℝ)*S) := by
  have _ := hS
  have hp : (0 : ℝ) < B.p := by exact_mod_cast B.prime.pos
  have hsum : |∑ k, ((w k j).val : ℝ)*l k| ≤ (d : ℝ)*((B.p : ℝ)*S) := by
    calc
      _ ≤ ∑ k, |((w k j).val : ℝ)*l k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin d, (B.p : ℝ)*S := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
        apply mul_le_mul _ (hl k) (abs_nonneg _) (Nat.cast_nonneg _)
        exact_mod_cast (ZMod.val_lt (w k j)).le
      _ = _ := by simp
  calc
    _ = B.h/(B.p : ℝ)*|∑ k, ((w k j).val : ℝ)*l k| := by
      rw [shiftDim,abs_mul,abs_of_pos (div_pos B.h_pos hp)]
    _ ≤ B.h/(B.p : ℝ)*((d : ℝ)*((B.p : ℝ)*S)) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg B.h_pos.le hp.le)
    _ = _ := by field_simp

lemma shift_bound (A B : Block) (w : Fin B.b → A.Group) (l : B.Vec)
    {S : ℝ} (hS : 0 ≤ S) (hl : ∀ j, |l j| ≤ S) (j : Fin A.b) :
    |A.shift B w l j| ≤ A.h*((B.b : ℝ)*S) := A.shiftDim_bound B.b w l hS hl j
end Block

lemma succ_le_two_power (n : ℕ) : n+1 ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

lemma inverse_factor_bound (m n : ℕ) :
    (n+1)*(m+2)^m ≤ (m+n+2)^(m+n) := by
  calc
    _ ≤ 2^n*(m+n+2)^m := Nat.mul_le_mul (succ_le_two_power n)
      (Nat.pow_le_pow_left (by omega) _)
    _ ≤ (m+n+2)^n*(m+n+2)^m := Nat.mul_le_mul_right _
      (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [←pow_add]; congr 1; omega

namespace Chain
variable {B : Block}
lemma injectLast_bound (c : Chain B) (t : B.Vec) {S : ℝ} (hS : 0 ≤ S)
    (ht : ∀ j, |t j| ≤ B.h*S) : ∀ j, |c.injectLast t j| ≤ c.heights j*S := by
  cases c with
  | base B => exact ht
  | append c B w =>
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa [injectLast,appendEquiv,heights] using mul_nonneg (c.heights_nonneg k) hS
    · simpa [injectLast,appendEquiv,heights] using ht k

lemma inverse_coordinate_bound (c : Chain B) (x : c.Vec) {S : ℝ} (hS : 0 ≤ S)
    (hx : ∀ j, |c.linear x j| ≤ c.heights j*S) :
    ∀ j, |x j| ≤ S*((c.dim+2 : ℕ) : ℝ)^c.dim := by
  induction c generalizing S with
  | base B =>
    intro j
    have hj := hx j
    change |B.h*x j| ≤ B.h*S at hj
    rw [abs_mul,abs_of_pos B.h_pos] at hj
    have hsmall := (mul_le_mul_iff_right₀ B.h_pos).mp hj
    exact hsmall.trans (le_mul_of_one_le_right hS (one_le_pow₀ (by norm_cast; omega) ))
  | @append A c B w ih =>
    let x₁ : c.Vec := fun j => x (Fin.castAdd B.b j)
    let x₂ : B.Vec := fun j => x (Fin.natAdd c.dim j)
    have hdec : x = Fin.append x₁ x₂ := by
      ext j
      refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [x₁,x₂]
    have hlin : (Chain.append c B w).linear x =
        Fin.append (c.linear x₁+c.injectLast (A.shift B w x₂)) (B.h • x₂) := by
      rw [hdec]
      change triangular c.linear B.linear (c.injectLast.comp (A.shiftMap B w))
        (Fin.append x₁ x₂) = _
      rw [triangular_append,LinearMap.comp_apply,Block.shiftMap_apply,Block.linear_apply]
    have h₂ : ∀ j, |x₂ j| ≤ S := by
      intro j
      have hj := hx (Fin.natAdd c.dim j)
      rw [hlin] at hj
      simp only [heights,Fin.append_right,Pi.smul_apply,smul_eq_mul] at hj
      rw [abs_mul,abs_of_pos B.h_pos] at hj
      exact (mul_le_mul_iff_right₀ B.h_pos).mp hj
    have hshift := c.injectLast_bound (A.shift B w x₂) (mul_nonneg (Nat.cast_nonneg _) hS)
      (A.shift_bound B w x₂ hS h₂)
    have h₁ : ∀ j, |c.linear x₁ j| ≤ c.heights j*((B.b+1 : ℕ)*S) := by
      intro j
      have hj := hx (Fin.castAdd B.b j)
      have hj' : |c.linear x₁ j + c.injectLast (A.shift B w x₂) j| ≤ c.heights j*S := by
        rw [hlin] at hj
        simpa only [heights,Fin.append_left,Pi.add_apply] using hj
      calc
        _ = |(c.linear x₁ j + c.injectLast (A.shift B w x₂) j)-
            c.injectLast (A.shift B w x₂) j| := by congr 1; ring
        _ ≤ |c.linear x₁ j + c.injectLast (A.shift B w x₂) j|+
            |c.injectLast (A.shift B w x₂) j| := abs_sub _ _
        _ ≤ c.heights j*S+c.heights j*((B.b : ℝ)*S) := add_le_add hj' (hshift j)
        _ = _ := by push_cast; ring
    have hb := ih x₁ (mul_nonneg (Nat.cast_nonneg _) hS) h₁
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · have hpow : (((B.b+1 : ℕ) : ℝ)*((c.dim+2 : ℕ) : ℝ)^c.dim) ≤
          ((c.dim+B.b+2 : ℕ) : ℝ)^(c.dim+B.b) := by
        exact_mod_cast inverse_factor_bound c.dim B.b
      calc
        _ ≤ ((B.b+1 : ℕ) : ℝ)*S*((c.dim+2 : ℕ) : ℝ)^c.dim := hb k
        _ = S*((B.b+1 : ℕ)*((c.dim+2 : ℕ) : ℝ)^c.dim) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hS
    · exact (h₂ k).trans (le_mul_of_one_le_right hS (one_le_pow₀ (by norm_cast; omega)))

end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry
open scoped BigOperators

namespace Chain
variable {B : Block}

lemma full_inverse_coordinate_bound (c : Chain B) (x : c.FullVec) {S : ℝ} (hS : 0 ≤ S)
    (hx : ∀ j, |c.fullLinear x j| ≤ (Fin.append c.heights (fun _ => 1)) j*S) :
    ∀ j, |x j| ≤ S*((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := by
  let x₁ : c.Vec := fun j => x (Fin.castAdd B.terminalDim j)
  let x₂ : Fin B.terminalDim → ℝ := fun j => x (Fin.natAdd c.dim j)
  have hdec : x = Fin.append x₁ x₂ := by
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [x₁,x₂]
  have hlin : c.fullLinear x = Fin.append (c.linear x₁+c.injectLast (B.terminalShift x₂)) x₂ := by
    rw [hdec]
    exact triangular_append c.linear (LinearEquiv.refl ℝ _) _ x₁ x₂
  have h₂ : ∀ j, |x₂ j| ≤ S := by
    intro j
    have hj := hx (Fin.natAdd c.dim j)
    rw [hlin] at hj
    simpa only [Fin.append_right,one_mul] using hj
  have hshift₀ : ∀ j, |B.terminalShift x₂ j| ≤ B.h*((B.terminalDim : ℝ)*S) := by
    simpa only [Block.terminalShift,Block.shiftDimMap_apply] using
      B.shiftDim_bound B.terminalDim (terminalColumns B.b B.p) x₂ hS h₂
  have hshift := c.injectLast_bound (B.terminalShift x₂)
    (mul_nonneg (Nat.cast_nonneg _) hS) hshift₀
  have h₁ : ∀ j, |c.linear x₁ j| ≤ c.heights j*((B.terminalDim+1 : ℕ)*S) := by
    intro j
    have hj := hx (Fin.castAdd B.terminalDim j)
    have hj' : |c.linear x₁ j + c.injectLast (B.terminalShift x₂) j| ≤ c.heights j*S := by
      rw [hlin] at hj
      simpa only [Fin.append_left,Pi.add_apply] using hj
    calc
      _ = |(c.linear x₁ j + c.injectLast (B.terminalShift x₂) j)-
          c.injectLast (B.terminalShift x₂) j| := by congr 1; ring
      _ ≤ |c.linear x₁ j + c.injectLast (B.terminalShift x₂) j|+
          |c.injectLast (B.terminalShift x₂) j| := abs_sub _ _
      _ ≤ c.heights j*S+c.heights j*((B.terminalDim : ℝ)*S) := add_le_add hj' (hshift j)
      _ = _ := by push_cast; ring
  have hb := c.inverse_coordinate_bound x₁ (mul_nonneg (Nat.cast_nonneg _) hS) h₁
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro k
  · have hpow : (((B.terminalDim+1 : ℕ) : ℝ)*((c.dim+2 : ℕ) : ℝ)^c.dim) ≤
        ((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := by
      exact_mod_cast inverse_factor_bound c.dim B.terminalDim
    calc
      _ ≤ ((B.terminalDim+1 : ℕ) : ℝ)*S*((c.dim+2 : ℕ) : ℝ)^c.dim := hb k
      _ = S*((B.terminalDim+1 : ℕ)*((c.dim+2 : ℕ) : ℝ)^c.dim) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hS
  · exact (h₂ k).trans (le_mul_of_one_le_right hS (one_le_pow₀ (by norm_cast; omega)))

lemma full_residual_physical (c : Chain B) (y l : c.FullVec) (hl : c.FullResidual y l) :
    ∀ j, |(y-c.fullLinear l) j| ≤ (Fin.append c.heights (fun _ => 1)) j := by
  have he : l=Fin.append (fun j => l (Fin.castAdd B.terminalDim j))
      (fun j => l (Fin.natAdd c.dim j)) := by
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k <;> simp
  rw [he,full_residual]
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro k
  · simpa only [Fin.append_left] using c.residual_physical _ _ hl.1 k
  · simpa only [Fin.append_right] using hl.2 k

def alphabetRadius (c : Chain B) : ℕ := 1+(c.fullDim+2)^c.fullDim


lemma raw_coordinate_bound (c : Chain B) (z l : c.FullVec)
    (hz : ∀ j, 0 ≤ z j ∧ z j < 1) (hl : c.FullResidual (c.fullLinear z) l) :
    ∀ j, |l j| ≤ (c.alphabetRadius : ℝ) := by
  have hx := c.full_residual_physical _ _ hl
  rw [←map_sub] at hx
  have hb := c.full_inverse_coordinate_bound (z-l) (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [mul_one] using hx)
  intro j
  calc
    _ = |z j-(z-l) j| := by simp
    _ ≤ |z j|+|(z-l) j| := abs_sub _ _
    _ ≤ 1+1*((c.fullDim+2 : ℕ) : ℝ)^c.fullDim := add_le_add
      (by rw [abs_of_nonneg (hz j).1]; exact (hz j).2.le) (hb j)
    _ = _ := by simp [alphabetRadius]

def denominators : {B : Block} → (c : Chain B) → Fin c.dim → ℕ
  | _, .base B => fun _ => B.p
  | _, .append c B _ => Fin.append c.denominators (fun _ => B.p)

def fullDenominators (c : Chain B) : Fin c.fullDim → ℕ :=
  Fin.append c.denominators (fun _ => 1)

lemma denominators_pos (c : Chain B) : ∀ j, 0 < c.denominators j := by
  induction c with
  | base B => exact fun _ => B.prime.pos
  | append c B w ih =>
    intro j
    exact Fin.addCases (fun k => by simpa [denominators] using ih k)
      (fun k => by simpa [denominators] using B.prime.pos) j

lemma raw_rational (c : Chain B) (l : c.Vec) (hl : c.RawMem l) :
    ∀ j, ∃ k : ℤ, l j=(k : ℝ)/(c.denominators j : ℝ) := by
  induction c with
  | base B =>
    obtain ⟨k,hk,hkl⟩ := hl
    intro j
    exact ⟨k j,(congr_fun hkl j).symm⟩
  | append c B w ih =>
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simpa only [denominators,Fin.append_left] using ih _ hl.1 k
    · obtain ⟨v,hv,hvl⟩ := hl.2
      refine ⟨v k,?_⟩
      simpa only [denominators,Fin.append_right,generator] using (congr_fun hvl k).symm

lemma full_raw_rational (c : Chain B) (l : c.FullVec) (hl : l ∈ c.fullRaw) :
    ∀ j, ∃ k : ℤ, l j=(k : ℝ)/(c.fullDenominators j : ℝ) := by
  have hl' : (fun j => l (Fin.castAdd B.terminalDim j)) ∈ c.rawLattice ∧
      (fun j => l (Fin.natAdd c.dim j)) ∈ integerLattice B.terminalDim := hl
  have h₁ := c.raw_rational _ ((c.mem_raw _).mp hl'.1)
  have h₂ := ((Pi.basisFun ℝ (Fin B.terminalDim)).mem_span_iff_repr_mem ℤ _).mp hl'.2
  intro j
  refine Fin.addCases ?_ ?_ j <;> intro k
  · simpa only [fullDenominators,Fin.append_left] using h₁ k
  · obtain ⟨v,hv⟩ := h₂ k
    refine ⟨v,?_⟩
    simpa [fullDenominators] using hv.symm

end Chain


noncomputable def rationalAlphabet (Q p : ℕ) : Finset ℝ :=
  (Finset.Icc (-(Q*p : ℤ)) (Q*p : ℤ)).image (fun k : ℤ => (k : ℝ)/(p : ℝ))

lemma mem_rationalAlphabet (Q p : ℕ) (hp : 0 < p) {x : ℝ}
    (hx : |x| ≤ (Q : ℝ)) (hk : ∃ k : ℤ, x=(k : ℝ)/(p : ℝ)) :
    x ∈ rationalAlphabet Q p := by
  classical
  obtain ⟨k,rfl⟩ := hk
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  rw [abs_div,abs_of_pos hpr,div_le_iff₀ hpr,abs_le] at hx
  apply Finset.mem_image.mpr
  refine ⟨k,Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
  · exact_mod_cast hx.1
  · exact_mod_cast hx.2

lemma rationalAlphabet_card (Q p : ℕ) : (rationalAlphabet Q p).card ≤ 2*Q*p+1 := by
  classical
  apply le_trans Finset.card_image_le
  rw [Int.card_Icc]
  have he : (Q : ℤ)*p+1-(-((Q : ℤ)*p)) = ((2*Q*p+1 : ℕ) : ℤ) := by push_cast; ring
  rw [he,Int.toNat_natCast]

noncomputable def Chain.alphabets {B : Block} (c : Chain B) : Fin c.fullDim → Finset ℝ :=
  fun j => rationalAlphabet c.alphabetRadius (c.fullDenominators j)

lemma Chain.mem_alphabets {B : Block} (c : Chain B) (z l : c.FullVec)
    (hz : ∀ j, 0 ≤ z j ∧ z j < 1) (hl : c.FullResidual (c.fullLinear z) l)
    (hmem : l ∈ c.fullRaw) : ∀ j, l j ∈ c.alphabets j := by
  intro j
  apply mem_rationalAlphabet _ _ _ (c.raw_coordinate_bound z l hz hl j)
    (c.full_raw_rational l hmem j)
  exact Fin.addCases (fun k => by simpa [Chain.fullDenominators] using c.denominators_pos k)
    (fun _ => by simp [Chain.fullDenominators]) j


end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
