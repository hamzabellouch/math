import OAI.Probability.TraceReconstruction.SourceOracle

namespace OAI

/-!
# Amplification

Oracle products, mixed powers, padding, warmup and nested template Hellinger estimates, overlap, and block assembly.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The literal product/concatenation decoder charges only coordinates at
 which the two deterministic input templates differ. -/
theorem OracleTracePair.mixed_tv {q E V : ℝ} {x y : List Bool} {k n : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1) (hk : 1≤k)
    (τ σ : Fin n → Bool) (M : ℕ)
    (hτ : (coordinateWord (fun i => if τ i then y else x)).length≤M)
    (hσ : (coordinateWord (fun i => if σ i then y else x)).length≤M) :
    (listTraceLaw q hq (coordinateWord (fun i => if τ i then y else x)) M hτ).tv
      (listTraceLaw q hq (coordinateWord (fun i => if σ i then y else x)) M hσ) ≤
      Real.sqrt ((∑i,if τ i=σ i then (0:ℝ) else 1)*V)+2*(n:ℝ)*E := by
  let := C.finiteOutcome
  have ha (ρ : Fin n → Bool) : ApproximatesTrace q
      (FiniteLaw.coordinateProduct (fun i => if ρ i then C.second else C.first))
      (fun z => coordinateWord (fun i => C.decode (z i)))
      (coordinateWord (fun i => if ρ i then y else x)) ((n:ℝ)*E) := by
    have H := coordinateProduct_approximates hq
      (fun i => if ρ i then C.second else C.first) (fun _ => C.decode)
      (fun i => if ρ i then y else x) (fun _ => E) (fun i => ?_)
    · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H
    · cases ρ i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact C.first_simulation
      · exact C.second_simulation
  have H := approximations_trace_tv hq _ _ _ _ _ _ _ M hτ hσ (ha τ) (ha σ)
  have htv := FiniteLaw.tv_mixedProduct_le C.first C.second C.score C.density k hk C.moment τ σ
  linarith only [H,htv]

theorem coordinateWord_constant (w : List Bool) (n : ℕ) :
    coordinateWord (fun _ : Fin n => w)=pureAtomRun w n := by
  induction n with
  | zero => simp [coordinateWord,pureAtomRun]
  | succ n ih =>
    rw [coordinateWord_succ,ih]
    simp only [pureAtomRun,List.replicate_succ,List.flatten_cons]

/-- Tensorization of a genuine approximate oracle, on actual word powers. -/
theorem OracleTracePair.power_tv {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1) (hk : 1≤k)
    (n M : ℕ) (hx : (pureAtomRun x n).length≤M) (hy : (pureAtomRun y n).length≤M) :
    (listTraceLaw q hq (pureAtomRun x n) M hx).tv
      (listTraceLaw q hq (pureAtomRun y n) M hy) ≤
      Real.sqrt ((n:ℝ)*V)+2*(n:ℝ)*E := by
  have H := C.mixed_tv hq hk (fun _ : Fin n => false) (fun _ => true) M
    (by simpa only [Bool.false_eq_true,ite_false,coordinateWord_constant] using hx)
    (by simpa only [ite_true,coordinateWord_constant] using hy)
  simpa only [Bool.false_eq_true,ite_false,ite_true,coordinateWord_constant,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using H

/-- Genuine lifting for complete traces, with no auxiliary overlap hypothesis. -/
theorem listTraceOverlap_lift {F k R : ℕ} {C p q : ℝ}
    (hk : 1≤k) (hR : 1≤R) (hp : p∈Set.Ioc 0 (1/8)) (hq : q∈Set.Icc 0 1)
    (hC : 1073741824≤p*C) (hF : C*k*R≤F) (w : List Bool)
    (hov : p≤listTraceOverlap q hq (pureAtomRun w k) (pureAtomRun w (k+1))) :
    (2/3:ℝ)≤listTraceOverlap q hq (pureAtomRun w (F*R)) (pureAtomRun w (F*R+R)) := by
  let M := max (pureAtomRun w k).length (pureAtomRun w (k+1)).length
  have H := adjacent_power_lift hk hR hp hq hC hF
    (listTraceLaw q hq (pureAtomRun w k) M (le_max_left _ _))
    (listTraceLaw q hq (pureAtomRun w (k+1)) M (le_max_right _ _)) Subtype.val w
    (listTraceLaw_simulates q hq _ M _) (listTraceLaw_simulates q hq _ M _) hov
  obtain ⟨β,fin,P,Q,g,hP,hQ,hO⟩ := H
  let := fin
  exact hO.trans (simulations_overlap_le hq P Q g _ _ hP hQ)

theorem pureAtomRun_mul (w : List Bool) (n m : ℕ) :
    pureAtomRun (pureAtomRun w n) m=pureAtomRun w (m*n) := by
  induction m with
  | zero => simp [pureAtomRun]
  | succ m ih =>
    have H : pureAtomRun (pureAtomRun w n) (m+1)=
        pureAtomRun w n++pureAtomRun (pureAtomRun w n) m := by
      simp [pureAtomRun,List.replicate_succ]
    rw [H,ih,←pureAtomRun_add]
    congr 1
    ring

/-- Quantitative overlap transfer used for the initial pure comparison and
 the small-dimensional warmup refinement. All three laws are ordinary traces. -/
theorem OracleTracePair.lifted_power_overlap {q E V p C₀ : ℝ} {w z : List Bool}
    {k h P F : ℕ} (O : OracleTracePair q (pureAtomRun w P) z k E V)
    (hq : q∈Set.Icc 0 1) (hk : 1≤k) (hh : 1≤h) (hP : 1≤P)
    (hp : p∈Set.Ioc 0 (1/8)) (hC : 1073741824≤p*C₀) (hF : C₀*h*P≤F)
    (hov : p≤listTraceOverlap q hq (pureAtomRun w h) (pureAtomRun w (h+1))) :
    (2/3:ℝ)-(Real.sqrt ((F:ℝ)*V)+2*(F:ℝ)*E)-
      (Real.sqrt (((F+1:ℕ):ℝ)*V)+2*((F+1:ℕ):ℝ)*E) ≤
      listTraceOverlap q hq (pureAtomRun z F) (pureAtomRun z (F+1)) := by
  let a := pureAtomRun (pureAtomRun w P) F
  let b := pureAtomRun (pureAtomRun w P) (F+1)
  let x := pureAtomRun z F
  let y := pureAtomRun z (F+1)
  let M := max (max a.length b.length) (max x.length y.length)
  have ha : a.length≤M := (le_max_left _ _).trans (le_max_left _ _)
  have hb : b.length≤M := (le_max_right _ _).trans (le_max_left _ _)
  have hx : x.length≤M := (le_max_left _ _).trans (le_max_right _ _)
  have hy : y.length≤M := (le_max_right _ _).trans (le_max_right _ _)
  have ht1 := O.power_tv hq hk F M ha hx
  have ht2 := O.power_tv hq hk (F+1) M hb hy
  have hol := listTraceOverlap_lift hh hP hp hq hC hF w hov
  have he : F*P+P=(F+1)*P := by ring
  have heA : pureAtomRun w (F*P)=a := (pureAtomRun_mul w P F).symm
  have heB : pureAtomRun w (F*P+P)=b := by
    rw [he]; exact (pureAtomRun_mul w P (F+1)).symm
  rw [heA,heB] at hol
  rw [listTraceOverlap_ambient hq _ _ M ha hb,FiniteLaw.overlap_eq_one_sub_tv] at hol
  rw [listTraceOverlap_ambient hq _ _ M hx hy,FiniteLaw.overlap_eq_one_sub_tv]
  have H := (FiniteLaw.tv_triangle (listTraceLaw q hq x M hx) (listTraceLaw q hq a M ha)
    (listTraceLaw q hq y M hy)).trans
    (add_le_add le_rfl (FiniteLaw.tv_triangle (listTraceLaw q hq a M ha)
      (listTraceLaw q hq b M hb) (listTraceLaw q hq y M hy)))
  rw [FiniteLaw.tv_symm (listTraceLaw q hq x M hx) (listTraceLaw q hq a M ha)] at H
  linarith only [H,ht1,ht2,hol]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace FiniteLaw
variable {α : Type*} [Fintype α]

theorem hellingerSq_mixedProduct_le {n : ℕ} (P Q : FiniteLaw α) {V : ℝ}
    (hH : P.hellingerSq Q ≤ V) (τ σ : Fin n → Bool) :
    (coordinateProduct (fun i => if τ i then Q else P)).hellingerSq
      (coordinateProduct (fun i => if σ i then Q else P)) ≤
      (∑i,if τ i=σ i then (0:ℝ) else 1)*V := by
  apply (hellingerSq_coordinateProduct_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  cases τ i <;> cases σ i <;> simp only [Bool.false_eq_true,Bool.true_eq_false,
    ite_false,ite_true,zero_mul,one_mul,hellingerSq_self,le_refl]
  · exact hH
  · rw [hellingerSq_symm]; exact hH

end FiniteLaw

theorem ApproximatesTrace.power {α : Type*} [Fintype α] {q E : ℝ} {P : FiniteLaw α}
    {g : α → List Bool} {w : List Bool} (H : ApproximatesTrace q P g w E)
    (hq : q∈Set.Icc 0 1) (F : ℕ) :
    ApproximatesTrace q (P.product F) (fun z => coordinateWord (fun i => g (z i)))
      (pureAtomRun w F) ((F:ℝ)*E) := by
  have h := coordinateProduct_approximates hq (fun _ : Fin F => P) (fun _ => g)
    (fun _ => w) (fun _ => E) (fun _ => H)
  have he : FiniteLaw.coordinateProduct (fun _ : Fin F => P)=P.product F := rfl
  rw [he,coordinateWord_constant] at h
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

/-- Repeated mixed templates pay only for the differing leaves in squared
 Hellinger, while approximate leaf simulation is charged linearly. -/
theorem OracleTracePair.mixed_power_tv {q E V : ℝ} {x y : List Bool} {k n : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1) (hk : 1 ≤ k)
    (τ σ : Fin n → Bool) (F M : ℕ)
    (hτ : (pureAtomRun (coordinateWord (fun i => if τ i then y else x)) F).length ≤ M)
    (hσ : (pureAtomRun (coordinateWord (fun i => if σ i then y else x)) F).length ≤ M) :
    (listTraceLaw q hq (pureAtomRun (coordinateWord (fun i => if τ i then y else x)) F) M hτ).tv
      (listTraceLaw q hq (pureAtomRun (coordinateWord (fun i => if σ i then y else x)) F) M hσ) ≤
      Real.sqrt ((F:ℝ)*(∑i,if τ i=σ i then (0:ℝ) else 1)*V)+2*(F:ℝ)*(n:ℝ)*E := by
  let := C.finiteOutcome
  let A (ρ : Fin n → Bool) := FiniteLaw.coordinateProduct (fun i => if ρ i then C.second else C.first)
  let g (z : Fin n → C.Outcome) := coordinateWord (fun i => C.decode (z i))
  have ha (ρ : Fin n → Bool) : ApproximatesTrace q (A ρ) g
      (coordinateWord (fun i => if ρ i then y else x)) ((n:ℝ)*E) := by
    have H := coordinateProduct_approximates hq
      (fun i => if ρ i then C.second else C.first) (fun _ => C.decode)
      (fun i => if ρ i then y else x) (fun _ => E) (fun i => ?_)
    · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H
    · cases ρ i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact C.first_simulation
      · exact C.second_simulation
  have hH : C.first.hellingerSq C.second ≤ V :=
    (C.first.hellingerSq_le_score C.second C.score C.density).trans
      ((C.first.secondMoment_le_evenMomentSq C.score k hk).trans C.moment)
  have hm := FiniteLaw.hellingerSq_mixedProduct_le C.first C.second hH τ σ
  have hp := (FiniteLaw.hellingerSq_product_le (A τ) (A σ) F).trans
    (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg F))
  have htv := (FiniteLaw.tv_le_sqrt_hellingerSq ((A τ).product F) ((A σ).product F)).trans
    (Real.sqrt_le_sqrt hp)
  have H := approximations_trace_tv hq _ _ _ _ _ _ _ M hτ hσ
    ((ha τ).power hq F) ((ha σ).power hq F)
  rw [←mul_assoc] at htv
  linarith only [H,htv]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- An exact common prefix and suffix are observed as ordinary independent
 complete traces. They neither change the score moment nor cost simulation
 error. This is the source's deterministic residual convention. -/
def OracleTracePair.pad {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1) (u v : List Bool) :
    OracleTracePair q (u++x++v) (u++y++v) k E V := by
  let := C.finiteOutcome
  let P := listTraceLaw q hq u u.length le_rfl
  let Q := listTraceLaw q hq v v.length le_rfl
  refine {
    Outcome := (BoundedTrace u.length × C.Outcome) × BoundedTrace v.length
    finiteOutcome := inferInstance
    first := (P.prod C.first).prod Q
    second := (P.prod C.second).prod Q
    decode := fun z => z.1.1.val++C.decode z.1.2++z.2.val
    score := fun z => C.score z.1.2
    density := by
      intro z
      change (P.mass z.1.1*C.second.mass z.1.2)*Q.mass z.2=_
      rw [C.density]
      change _=(P.mass z.1.1*C.first.mass z.1.2)*Q.mass z.2*(1+C.score z.1.2)
      ring
    likelihood_nonneg := fun z => C.likelihood_nonneg z.1.2
    centered := by
      simp only [FiniteLaw.expect_prod,FiniteLaw.expect_const,C.centered]
    moment := by
      simpa only [FiniteLaw.evenMomentSq,FiniteLaw.expect_prod,FiniteLaw.expect_const] using C.moment
    first_simulation := by
      have H := ((listTraceLaw_simulates q hq u u.length le_rfl).approximate.append hq
        C.first_simulation).append hq (listTraceLaw_simulates q hq v v.length le_rfl).approximate
      simpa only [zero_add,add_zero] using H
    second_simulation := by
      have H := ((listTraceLaw_simulates q hq u u.length le_rfl).approximate.append hq
        C.second_simulation).append hq (listTraceLaw_simulates q hq v v.length le_rfl).approximate
      simpa only [zero_add,add_zero] using H }

/-- Literal template equality under deterministic pure residual padding. -/
theorem complementaryWords_pad (L P R a len : ℕ) (sign : Fin len → Bool)
    (w : Bool → List Bool) (τ : Bool) (hfit : a+len ≤ P) :
    complementaryWords (L+P+R) (L+a) len sign w τ =
      pureAtomRun (w false) L++complementaryWords P a len sign w τ++pureAtomRun (w false) R := by
  unfold complementaryWords
  rw [atomString_three]
  have hp (i : Fin L) : templateType (L+P+R) (L+a) len sign τ ⟨i.val,by omega⟩=false := by
    have hi := i.isLt
    simp only [templateType,dite_eq_right (by omega : ¬(L+a ≤ i.val ∧ i.val < L+a+len))]
  have hm (i : Fin P) : templateType (L+P+R) (L+a) len sign τ ⟨L+i.val,by omega⟩=
      templateType P a len sign τ i := by
    unfold templateType
    split_ifs with h h' h'
    · congr 2
      apply Fin.ext
      simp only
      omega
    · simp only at h
      omega
    · simp only at h
      omega
    · rfl
  have hr (i : Fin R) : templateType (L+P+R) (L+a) len sign τ ⟨L+P+i.val,by omega⟩=false := by
    simp only [templateType,dite_eq_right (by omega : ¬(L+a ≤ L+P+i.val ∧ L+P+i.val < L+a+len))]
  simp_rw [hp,hm,hr]
  change coordinateWord (fun _ : Fin L => w false)++_++coordinateWord (fun _ : Fin R => w false)=_
  rw [coordinateWord_constant,coordinateWord_constant]

def centeredLeftResidual (N P : ℕ) : ℕ := N/2-1-(P/2-1)
def centeredRightResidual (N P : ℕ) : ℕ := N-(centeredLeftResidual N P+P)

theorem centeredResidual_geometry {N P : ℕ} (hP : 2 ≤ P) (hN : P ≤ N) :
    centeredLeftResidual N P+P+centeredRightResidual N P=N ∧
    centeredLeftResidual N P+(P/2-1)=N/2-1 := by
  simp only [centeredRightResidual,centeredLeftResidual]
  omega

/-- The auxiliary one-window oracle is centered at the same actual source
 motif after appending pure residuals, also for odd ambient atom counts. -/
theorem centeredComplementaryWords_pad (N P s : ℕ) (w : Bool → List Bool) (τ : Bool)
    (hP : 2 ≤ P) (hN : P ≤ N) (hfit : P/2-1+2^s ≤ P) :
    complementaryWords N (N/2-1) (2^s) (prouhetBool s) w τ =
      pureAtomRun (w false) (centeredLeftResidual N P)++
      complementaryWords P (P/2-1) (2^s) (prouhetBool s) w τ++
      pureAtomRun (w false) (centeredRightResidual N P) := by
  have h := complementaryWords_pad (centeredLeftResidual N P) P (centeredRightResidual N P)
    (P/2-1) (2^s) (prouhetBool s) w τ hfit
  rw [(centeredResidual_geometry hP hN).1,(centeredResidual_geometry hP hN).2] at h
  exact h

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The source's special one-window warmup observation. The ambient word
 need not have the root's arithmetic divisibility: exact pure residuals
 restore its literal center, at no additional statistical error. -/
theorem actual_one_window_oracle {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1) (hE : 0 ≤ E)
    (s N T t h R : ℕ) (hT : 24 ≤ T) (he : Even T)
    (hMotif : 24*2^s ≤ T) (hroot : 4*(t+1) ≤ T)
    (hfit : t*(2*h+1)+T ≤ N)
    (ω a η L : ℝ) (ha : 0 < a) (hL : 0 < L) (hω : ω∈Set.Ioo 0 1)
    (hov : ω ≤ listTraceOverlap q hq (pureAtomRun x h) (pureAtomRun x (h+1)))
    (hk : 1 ≤ k) (hV : V ≤ L^2)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount (fun _ => T) s 0 ≤ 1/2)
    (hη : hiddenSmoothingBound t s ω ≤ η)
    (herror : sourceClippingCost (fun _ => T) (fun _ => t) s 0 k ω a L ≤ 1/2) :
    Nonempty (OracleTracePair q
      (complementaryWords N (N/2-1) (2^s) (prouhetBool s) (fun τ => if τ then y else x) false)
      (complementaryWords N (N/2-1) (2^s) (prouhetBool s) (fun τ => if τ then y else x) true) k
      (sourceClippingCost (fun _ => T) (fun _ => t) s 0 k ω a L+(T:ℝ)*E)
      (64*sourceSharpEnergyBudget (fun _ => T) (fun _ => t) s 0 R ω η a ((6*(2*k:ℕ):ℝ)*L))) := by
  let := C.finiteOutcome
  let p := t*(2*h+1)+T
  let atom : Bool → List Bool := fun τ => if τ then y else x
  have H : SourceLayoutMargins s (fun _ => p) (fun _ => T) (fun _ => t) (fun _ => h) 0 := by
    constructor <;> intro j hj <;> omega
  have hm : C.first.expect (fun z => |C.score z|^(2*k)) ≤ L^(2*k) := by
    have hv := C.first.expect_even_pow_le_of_moment C.score k hk (C.moment.trans hV)
    simpa only [pow_mul] using hv
  obtain ⟨W⟩ := actual_source_oracle hq hE s (fun _ => p) (fun _ => T) (fun _ => t)
    (fun _ => h) atom 0 R k H (fun _ => by omega) rfl
    (fun j hj => by omega) (fun _ _ => hT) (fun _ _ => he) (fun _ _ => hMotif) hroot
    C.first C.second C.decode C.score C.density C.likelihood_nonneg
    C.first_simulation C.second_simulation ω a η L ha hL hω
    (fun j hj => by
      have hj' : j=0 := by omega
      subst j
      exact hov)
    hk hm hscale (fun _ _ => hη) herror
  have hp : 2 ≤ p := by dsimp [p]; omega
  have hmp : p/2-1+2^s ≤ p := by dsimp [p] at *; omega
  let U := pureAtomRun x (centeredLeftResidual N p)
  let B := pureAtomRun x (centeredRightResidual N p)
  have heq (τ : Bool) := centeredComplementaryWords_pad N p s atom τ hp hfit hmp
  have HH := W.pad hq U B
  simp only [sourceBlockWord,sourceFitTail,add_zero] at HH
  change OracleTracePair q
    (U++complementaryWords p (p/2-1) (2^s) (prouhetBool s) atom false++B)
    (U++complementaryWords p (p/2-1) (2^s) (prouhetBool s) atom true++B) k _ _ at HH
  have hleft : U++complementaryWords p (p/2-1) (2^s) (prouhetBool s) atom false++B =
      complementaryWords N (N/2-1) (2^s) (prouhetBool s) atom false := (heq false).symm
  have hright : U++complementaryWords p (p/2-1) (2^s) (prouhetBool s) atom true++B =
      complementaryWords N (N/2-1) (2^s) (prouhetBool s) atom true := (heq true).symm
  rw [hleft,hright] at HH
  have hc : SourceLeafCount (fun _ => T) 1=T := by
    calc
      _ = Fintype.card (Fin (T*1)) := Fintype.card_congr finProdFinEquiv
      _ = T := by simp
  simp only [hc] at HH
  exact ⟨HH⟩

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem sourceLeafCount_one (T : ℕ → ℕ) : SourceLeafCount T 1=T 0 := by
  calc
    _ = Fintype.card (Fin (T 0*1)) := Fintype.card_congr finProdFinEquiv
    _ = T 0 := by simp

/-- Exact two-degree cutoff for the one-window warmup refinement. In
 particular the remaining geometric term is quadratic in the old energy. -/
theorem sourceSharpEnergyBudget_one_window (T n : ℕ → ℕ) (s : ℕ) (ω η a w : ℝ) :
    sourceSharpEnergyBudget T n s 0 2 ω η a w =
      36*(T 0:ℝ)*w^2*(η^2+a^2)+4*(w^2*2^s)^2/(1-w^2*2^s) := by
  simp only [sourceSharpEnergyBudget,Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [sourceSharpDegreeBudget,sourceSparseCount,sourceLeafCount_one,Nat.choose_one_right]
  ring

theorem sourceSharpEnergyBudget_warmup (T n : ℕ → ℕ) (s : ℕ) (ω η w : ℝ)
    (h : w^2*2^s ≤ 1/2) :
    sourceSharpEnergyBudget T n s 0 2 ω η η w ≤
      72*(T 0:ℝ)*w^2*η^2+8*(w^2*2^s)^2 := by
  rw [sourceSharpEnergyBudget_one_window]
  have hd : 0 < 1-w^2*2^s := by linarith
  have hb : 4*(w^2*2^s)^2/(1-w^2*2^s) ≤ 8*(w^2*2^s)^2 := by
    apply (div_le_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (w^2*2^s))
    nlinarith only [hh]
  nlinarith only [hb]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- The number of differing labels of complementary templates is bounded
 by the actual motif length, without any assumption that it fills the word. -/
theorem templateType_difference_count (N a L : ℕ) (sign : Fin L → Bool) (τ σ : Bool) :
    (∑i : Fin N,if templateType N a L sign τ i=templateType N a L sign σ i then (0:ℝ) else 1) ≤ L := by
  let S : Finset (Fin N) := Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a+L)
  have hi (i : S) : a ≤ i.val.val ∧ i.val.val < a+L := (Finset.mem_filter.mp i.property).2
  let f : S → Fin L := fun i => ⟨i.val.val-a,by have h := hi i; omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h := congrArg Fin.val hij
    have h₁ := hi i
    have h₂ := hi j
    dsimp [f] at h
    apply Subtype.ext
    apply Fin.ext
    omega
  have hc : S.card ≤ L := by
    simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf
  calc
    _ ≤ ∑i : Fin N,if i∈S then (1:ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : i∈S
      · rw [ite_eq_left h]; split_ifs <;> norm_num
      · have h' : ¬(a ≤ i.val ∧ i.val < a+L) := by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using h
        simp [templateType,h',h]
    _ = (S.card:ℝ) := by simp
    _ ≤ L := by exact_mod_cast hc

/-- Actual paired finite observations with a common complete-trace decoder
 and a squared Hellinger bound. This auxiliary structure is constructed from
 the source score oracle and closed under literal template substitution. -/
structure HellingerTracePair (q : ℝ) (x y : List Bool) (E V : ℝ) where
  Outcome : Type
  finiteOutcome : Fintype Outcome
  first : @FiniteLaw Outcome finiteOutcome
  second : @FiniteLaw Outcome finiteOutcome
  decode : Outcome → List Bool
  first_simulation : @ApproximatesTrace Outcome finiteOutcome q first decode x E
  second_simulation : @ApproximatesTrace Outcome finiteOutcome q second decode y E
  bound : @FiniteLaw.hellingerSq Outcome finiteOutcome first second ≤ V

def OracleTracePair.hellinger {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) (hk : 1 ≤ k) : HellingerTracePair q x y E V := by
  let := C.finiteOutcome
  exact {
    Outcome := C.Outcome
    finiteOutcome := C.finiteOutcome
    first := C.first
    second := C.second
    decode := C.decode
    first_simulation := C.first_simulation
    second_simulation := C.second_simulation
    bound := (C.first.hellingerSq_le_score C.second C.score C.density).trans
      ((C.first.secondMoment_le_evenMomentSq C.score k hk).trans C.moment) }

def HellingerTracePair.mix {q E V : ℝ} {x y : List Bool} (C : HellingerTracePair q x y E V)
    (hq : q∈Set.Icc 0 1) {N : ℕ} (τ σ : Fin N → Bool) :
    HellingerTracePair q (coordinateWord (fun i => if τ i then y else x))
      (coordinateWord (fun i => if σ i then y else x)) ((N:ℝ)*E)
      ((∑i,if τ i=σ i then (0:ℝ) else 1)*V) := by
  let := C.finiteOutcome
  have ha (ρ : Fin N → Bool) : ApproximatesTrace q
      (FiniteLaw.coordinateProduct (fun i => if ρ i then C.second else C.first))
      (fun z => coordinateWord (fun i => C.decode (z i)))
      (coordinateWord (fun i => if ρ i then y else x)) ((N:ℝ)*E) := by
    have H := coordinateProduct_approximates hq
      (fun i => if ρ i then C.second else C.first) (fun _ => C.decode)
      (fun i => if ρ i then y else x) (fun _ => E) (fun i => ?_)
    · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H
    · cases ρ i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact C.first_simulation
      · exact C.second_simulation
  exact {
    Outcome := Fin N → C.Outcome
    finiteOutcome := inferInstance
    first := FiniteLaw.coordinateProduct (fun i => if τ i then C.second else C.first)
    second := FiniteLaw.coordinateProduct (fun i => if σ i then C.second else C.first)
    decode := fun z => coordinateWord (fun i => C.decode (z i))
    first_simulation := ha τ
    second_simulation := ha σ
    bound := FiniteLaw.hellingerSq_mixedProduct_le C.first C.second C.bound τ σ }

def HellingerTracePair.weaken {q E V W : ℝ} {x y : List Bool}
    (C : HellingerTracePair q x y E V) (h : V ≤ W) : HellingerTracePair q x y E W :=
  { C with bound := C.bound.trans h }

def HellingerTracePair.template {q E V : ℝ} {x y : List Bool} (C : HellingerTracePair q x y E V)
    (hq : q∈Set.Icc 0 1) (N a L : ℕ) (sign : Fin L → Bool) :
    HellingerTracePair q
      (complementaryWords N a L sign (fun τ => if τ then y else x) false)
      (complementaryWords N a L sign (fun τ => if τ then y else x) true) ((N:ℝ)*E) ((L:ℝ)*V) := by
  let := C.finiteOutcome
  let D := C.mix hq (templateType N a L sign false) (templateType N a L sign true)
  have hV : 0 ≤ V := (FiniteLaw.hellingerSq_nonneg _ _).trans C.bound
  exact D.weaken (mul_le_mul_of_nonneg_right (templateType_difference_count N a L sign false true) hV)

theorem HellingerTracePair.power_tv {q E V : ℝ} {x y : List Bool}
    (C : HellingerTracePair q x y E V) (hq : q∈Set.Icc 0 1)
    (F M : ℕ) (hx : (pureAtomRun x F).length ≤ M) (hy : (pureAtomRun y F).length ≤ M) :
    (listTraceLaw q hq (pureAtomRun x F) M hx).tv
      (listTraceLaw q hq (pureAtomRun y F) M hy) ≤ Real.sqrt ((F:ℝ)*V)+2*(F:ℝ)*E := by
  let := C.finiteOutcome
  have htv := (FiniteLaw.tv_le_sqrt_hellingerSq (C.first.product F) (C.second.product F)).trans
    (Real.sqrt_le_sqrt ((FiniteLaw.hellingerSq_product_le C.first C.second F).trans
      (mul_le_mul_of_nonneg_left C.bound (Nat.cast_nonneg F))))
  have H := approximations_trace_tv hq _ _ _ _ _ _ _ M hx hy
    (C.first_simulation.power hq F) (C.second_simulation.power hq F)
  linarith only [H,htv]

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem templateType_one_count (N a L : ℕ) (sign : Fin L → Bool) (τ : Bool) :
    (∑i : Fin N,if false=templateType N a L sign τ i then (0:ℝ) else 1) ≤ L := by
  apply le_trans _ (templateType_difference_count N a L sign false true)
  apply Finset.sum_le_sum
  intro i _
  by_cases h : a ≤ i.val ∧ i.val < a+L
  · simp only [templateType,dite_eq_left h]
    cases hs : sign ⟨i.val-a,by omega⟩ <;> cases τ <;> norm_num
  · simp [templateType,h]

def HellingerTracePair.pure_template {q E V : ℝ} {x y : List Bool}
    (C : HellingerTracePair q x y E V) (hq : q∈Set.Icc 0 1)
    (N a L : ℕ) (sign : Fin L → Bool) (τ : Bool) :
    HellingerTracePair q (pureAtomRun x N)
      (complementaryWords N a L sign (fun υ => if υ then y else x) τ) ((N:ℝ)*E) ((L:ℝ)*V) := by
  let := C.finiteOutcome
  let D := C.mix hq (fun _ : Fin N => false) (templateType N a L sign τ)
  have hV : 0 ≤ V := (FiniteLaw.hellingerSq_nonneg _ _).trans C.bound
  have W := D.weaken (mul_le_mul_of_nonneg_right (templateType_one_count N a L sign τ) hV)
  simp only [Bool.false_eq_true,ite_false,coordinateWord_constant] at W
  exact W

theorem bool_word_eta (w : Bool → List Bool) : (fun τ => if τ then w true else w false)=w := by
  funext τ
  cases τ <;> rfl

/-- Literal dense substitution of the old auxiliary laws, used only for
 overlap comparison. Statistical cost is paid only for differing motif
 leaves, not the filler atoms. -/
def sourceDensePair {q E V : ℝ} (hq : q∈Set.Icc 0 1) (s : ℕ) (P : ℕ → ℕ)
    (atom : Bool → List Bool) (C : HellingerTracePair q (atom false) (atom true) E V) :
    (j : ℕ) → HellingerTracePair q (sourceBlockWord s P atom j false)
      (sourceBlockWord s P atom j true) ((sourceBlockLength P 1 j:ℝ)*E) (((2^s:ℕ):ℝ)^j*V)
  | 0 => by simpa only [sourceBlockWord,sourceBlockLength,Nat.cast_one,pow_zero,one_mul] using C
  | j+1 => by
      have D := (sourceDensePair hq s P atom C j).template hq (P j) (P j/2-1) (2^s) (prouhetBool s)
      rw [bool_word_eta] at D
      simpa only [sourceBlockWord,sourceBlockLength,Nat.cast_mul,pow_succ,
        mul_assoc,mul_left_comm,mul_comm] using D

theorem HellingerTracePair.lifted_power_overlap {q E V p C₀ : ℝ} {w z : List Bool}
    {h P F : ℕ} (O : HellingerTracePair q (pureAtomRun w P) z E V)
    (hq : q∈Set.Icc 0 1) (hh : 1 ≤ h) (hP : 1 ≤ P)
    (hp : p∈Set.Ioc 0 (1/8)) (hC : 1073741824 ≤ p*C₀) (hF : C₀*h*P ≤ F)
    (hov : p ≤ listTraceOverlap q hq (pureAtomRun w h) (pureAtomRun w (h+1))) :
    (2/3:ℝ)-(Real.sqrt ((F:ℝ)*V)+2*(F:ℝ)*E)-
      (Real.sqrt (((F+1:ℕ):ℝ)*V)+2*((F+1:ℕ):ℝ)*E) ≤
      listTraceOverlap q hq (pureAtomRun z F) (pureAtomRun z (F+1)) := by
  let a := pureAtomRun (pureAtomRun w P) F
  let b := pureAtomRun (pureAtomRun w P) (F+1)
  let x := pureAtomRun z F
  let y := pureAtomRun z (F+1)
  let M := max (max a.length b.length) (max x.length y.length)
  have ha : a.length ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hb : b.length ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hx : x.length ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hy : y.length ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  have ht1 := O.power_tv hq F M ha hx
  have ht2 := O.power_tv hq (F+1) M hb hy
  have hol := listTraceOverlap_lift hh hP hp hq hC hF w hov
  have he : F*P+P=(F+1)*P := by ring
  have heA : pureAtomRun w (F*P)=a := (pureAtomRun_mul w P F).symm
  have heB : pureAtomRun w (F*P+P)=b := by
    rw [he]; exact (pureAtomRun_mul w P (F+1)).symm
  rw [heA,heB] at hol
  rw [listTraceOverlap_ambient hq _ _ M ha hb,FiniteLaw.overlap_eq_one_sub_tv] at hol
  rw [listTraceOverlap_ambient hq _ _ M hx hy,FiniteLaw.overlap_eq_one_sub_tv]
  have H := (FiniteLaw.tv_triangle (listTraceLaw q hq x M hx) (listTraceLaw q hq a M ha)
    (listTraceLaw q hq y M hy)).trans
    (add_le_add le_rfl (FiniteLaw.tv_triangle (listTraceLaw q hq a M ha)
      (listTraceLaw q hq b M hb) (listTraceLaw q hq y M hy)))
  rw [FiniteLaw.tv_symm (listTraceLaw q hq x M hx) (listTraceLaw q hq a M ha)] at H
  linarith only [H,ht1,ht2,hol]

theorem HellingerTracePair.lifted_overlap_quarter {q E V p C₀ : ℝ} {w z : List Bool}
    {h P F : ℕ} (O : HellingerTracePair q (pureAtomRun w P) z E V)
    (hq : q∈Set.Icc 0 1) (hE : 0 ≤ E) (hh : 1 ≤ h) (hP : 1 ≤ P)
    (hp : p∈Set.Ioc 0 (1/8)) (hC : 1073741824 ≤ p*C₀) (hF : C₀*h*P ≤ F)
    (hov : p ≤ listTraceOverlap q hq (pureAtomRun w h) (pureAtomRun w (h+1)))
    (hsmall : Real.sqrt (((F+1:ℕ):ℝ)*V)+2*((F+1:ℕ):ℝ)*E ≤ 1/4) :
    p ≤ listTraceOverlap q hq (pureAtomRun z F) (pureAtomRun z (F+1)) := by
  let := O.finiteOutcome
  have hV : 0 ≤ V := (FiniteLaw.hellingerSq_nonneg _ _).trans O.bound
  have ht := O.lifted_power_overlap hq hh hP hp hC hF hov
  have hm : Real.sqrt ((F:ℝ)*V)+2*(F:ℝ)*E ≤
      Real.sqrt (((F+1:ℕ):ℝ)*V)+2*((F+1:ℕ):ℝ)*E := by
    apply add_le_add
    · apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_right (by norm_num) hV
    · exact mul_le_mul_of_nonneg_right (by norm_num) hE
  linarith only [hm,hsmall,ht,hp.2]

/-- Finite nested overlap induction at the main (post-warmup) dimensions.
 Every closeness premise is an explicit scalar estimate on the old oracle;
 the repeated-word overlaps themselves are proved, not assumed. -/
theorem source_nested_overlap {q E V p C₀ : ℝ} (hq : q∈Set.Icc 0 1)
    (hE : 0 ≤ E) (s : ℕ) (P h : ℕ → ℕ) (atom : Bool → List Bool)
    (C : HellingerTracePair q (atom false) (atom true) E V) (b : ℕ)
    (hp : p∈Set.Ioc 0 (1/8)) (hC : 1073741824 ≤ p*C₀)
    (hcount : ∀j ≤ b,1 ≤ h j) (hP : ∀j < b,1 ≤ P j)
    (hlift : ∀j < b,C₀*h j*P j ≤ h (j+1))
    (hsmall : ∀j < b,
      Real.sqrt (((h (j+1)+1:ℕ):ℝ)*(((2^s:ℕ):ℝ)^(j+1)*V))+
        2*((h (j+1)+1:ℕ):ℝ)*((sourceBlockLength P 1 (j+1):ℝ)*E) ≤ 1/4)
    (hbase : p ≤ listTraceOverlap q hq (pureAtomRun (atom false) (h 0))
      (pureAtomRun (atom false) (h 0+1))) :
    ∀j ≤ b,p ≤ listTraceOverlap q hq (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)) := by
  intro j hj
  induction j with
  | zero => exact hbase
  | succ j ih =>
    have hjb : j < b := by omega
    have D := (sourceDensePair hq s P atom C j).pure_template hq (P j) (P j/2-1) (2^s) (prouhetBool s) false
    rw [bool_word_eta] at D
    have H := D.lifted_overlap_quarter hq (by positivity) (hcount j (by omega)) (hP j hjb)
      hp hC (hlift j hjb) (ih (by omega)) ?_
    · exact H
    · simpa only [sourceBlockLength,Nat.cast_mul,pow_succ,mul_assoc,mul_left_comm,mul_comm]
        using hsmall j hjb

end TraceReconstruction



noncomputable section
namespace TraceReconstruction
open scoped Classical


theorem sourceFitTail_nonneg (T n : ℕ → ℕ) (b : ℕ) : 0 ≤ sourceFitTail T n b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    cases b with
    | zero => rfl
    | succ b => exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg (by positivity) ih)

theorem sourceEffectiveHiddenTail_nonneg (T n : ℕ → ℕ) (b : ℕ) (ω : ℝ) :
    0 ≤ sourceEffectiveHiddenTail T n b ω := by
  apply Finset.sum_nonneg
  intro v _
  split_ifs <;> positivity

theorem sourceClippingCost_nonneg (T n : ℕ → ℕ) (s b k : ℕ) (ω a L : ℝ) (ha : 0 ≤ a) :
    0 ≤ sourceClippingCost T n s b k ω a L := by
  exact add_nonneg (add_nonneg (sourceEffectiveHiddenTail_nonneg _ _ _ _)
    (div_nonneg (sourceFitTail_nonneg _ _ _) ha)) (Real.sqrt_nonneg _)

/-- The two-dimensional warmup uses the actual one-window cancellation
 oracle at its second nested overlap step. No unproved side overlap is
 inserted into the recursive source observation. -/
theorem source_warmup_nested_overlap {q E V p C₀ : ℝ} (hq : q∈Set.Icc 0 1)
    (hE : 0 ≤ E) (s k : ℕ) (P h : ℕ → ℕ) (atom : Bool → List Bool)
    (C : OracleTracePair q (atom false) (atom true) k E V)
    (hp : p∈Set.Ioc 0 (1/8)) (hC : 1073741824 ≤ p*C₀)
    (hcount : ∀j ≤ 1,1 ≤ h j) (hP : ∀j < 2,1 ≤ P j)
    (hlift : ∀j < 2,C₀*h j*P j ≤ h (j+1))
    (hfirst : Real.sqrt (((h 1+1:ℕ):ℝ)*((2^s:ℕ):ℝ)*V)+
      2*((h 1+1:ℕ):ℝ)*((P 0:ℝ)*E) ≤ 1/4)
    (hbase : p ≤ listTraceOverlap q hq (pureAtomRun (atom false) (h 0))
      (pureAtomRun (atom false) (h 0+1)))
    (T t : ℕ) (hT : 24 ≤ T) (he : Even T) (hMotif : 24*2^s ≤ T)
    (hroot : 4*(t+1) ≤ T) (hfit : t*(2*h 0+1)+T ≤ P 0)
    (a η L : ℝ) (ha : 0 < a) (hL : 0 < L) (hk : 1 ≤ k) (hV : V ≤ L^2)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount (fun _ => T) s 0 ≤ 1/2)
    (hη : hiddenSmoothingBound t s p ≤ η)
    (herror : sourceClippingCost (fun _ => T) (fun _ => t) s 0 k p a L ≤ 1/2)
    (hsecond :
      Real.sqrt (((h 2+1:ℕ):ℝ)*((2^s:ℕ):ℝ)*
        (64*sourceSharpEnergyBudget (fun _ => T) (fun _ => t) s 0 2 p η a ((6*(2*k:ℕ):ℝ)*L)))+
      2*((h 2+1:ℕ):ℝ)*((P 1:ℝ)*
        (sourceClippingCost (fun _ => T) (fun _ => t) s 0 k p a L+(T:ℝ)*E)) ≤ 1/4) :
    ∀j ≤ 2,p ≤ listTraceOverlap q hq (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1)) := by
  have hp' : p∈Set.Ioo 0 1 := ⟨hp.1,lt_of_le_of_lt hp.2 (by norm_num)⟩
  have D := (C.hellinger hk).pure_template hq (P 0) (P 0/2-1) (2^s) (prouhetBool s) false
  rw [bool_word_eta] at D
  have h1 := D.lifted_overlap_quarter hq (by positivity) (hcount 0 (by omega))
    (hP 0 (by omega)) hp hC (hlift 0 (by omega)) hbase ?_
  · obtain ⟨W⟩ := actual_one_window_oracle C hq hE s (P 0) T t (h 0) 2 hT he hMotif
      hroot hfit p a η L ha hL hp' hbase hk hV hscale hη herror
    rw [bool_word_eta] at W
    have W' := (W.hellinger hk).pure_template hq (P 1) (P 1/2-1) (2^s) (prouhetBool s) false
    have heword : (fun τ => if τ then
        complementaryWords (P 0) (P 0/2-1) (2^s) (prouhetBool s) atom true else
        complementaryWords (P 0) (P 0/2-1) (2^s) (prouhetBool s) atom false) =
        sourceBlockWord s P atom 1 := bool_word_eta _
    rw [heword] at W'
    have hE' : 0 ≤ sourceClippingCost (fun _ => T) (fun _ => t) s 0 k p a L+(T:ℝ)*E := by
      exact add_nonneg (sourceClippingCost_nonneg _ _ _ _ _ _ _ _ ha.le) (by positivity)
    have h2 := W'.lifted_overlap_quarter hq (mul_nonneg (Nat.cast_nonneg _) hE')
      (hcount 1 le_rfl) (hP 1 (by omega)) hp hC (hlift 1 (by omega)) h1 ?_
    · intro j hj
      interval_cases j
      · exact hbase
      · exact h1
      · exact h2
    · simpa only [mul_assoc] using hsecond
  · simpa only [mul_assoc] using hfirst

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

theorem OracleTracePair.error_nonneg {q E V : ℝ} {x y : List Bool} {k : ℕ}
    (C : OracleTracePair q x y k E V) : 0 ≤ E := by
  let := C.finiteOutcome
  have h := C.first_simulation (fun _ => 0) (fun _ => ⟨le_rfl,zero_le_one⟩)
  exact (abs_nonneg _).trans h

/-- Finite main-block production: actual oracle, complete trace projection,
 and all side overlaps follow from arithmetic budgets and the OLD invariant.
 In particular none of the new side laws or their overlap are hypotheses. -/
theorem actual_main_block {q E V ω C₀ : ℝ} (hq : q∈Set.Icc 0 1)
    (s : ℕ) (P T n h : ℕ → ℕ) (atom : Bool → List Bool) (b R k : ℕ)
    (C : OracleTracePair q (atom false) (atom true) k E V)
    (H : SourceLayoutMargins s P T n h b)
    (hTpos : ∀j,0 < T j) (hP : P b=n b*(2*h b+1)+T b)
    (hn : ∀j < b,0 < n j) (hT : ∀j ≤ b,24 ≤ T j) (he : ∀j ≤ b,Even (T j))
    (hMotif : ∀j ≤ b,24*2^s ≤ T j) (hroot : 4*(n b+1) ≤ T b)
    (a η L : ℝ) (ha : 0 < a) (hL : 0 < L) (hω : ω∈Set.Ioc 0 (1/8))
    (hk : 1 ≤ k) (hV : V ≤ L^2)
    (hscale : ((6*(2*k:ℕ):ℝ)*L)^2*sourceSparseCount T s b ≤ 1/2)
    (hη : ∀j < b+1,hiddenSmoothingBound (n j) s ω ≤ η)
    (herror : sourceClippingCost T n s b k ω a L ≤ 1/2)
    (hC : 1073741824 ≤ ω*C₀) (hcount : ∀j ≤ b+1,1 ≤ h j)
    (hpos : ∀j < b+1,1 ≤ P j)
    (hlift : ∀j < b+1,C₀*h j*P j ≤ h (j+1))
    (hsmall : ∀j < b+1,
      Real.sqrt (((h (j+1)+1:ℕ):ℝ)*(((2^s:ℕ):ℝ)^(j+1)*V))+
        2*((h (j+1)+1:ℕ):ℝ)*((sourceBlockLength P 1 (j+1):ℝ)*E) ≤ 1/4)
    (hbase : ω ≤ listTraceOverlap q hq (pureAtomRun (atom false) (h 0))
      (pureAtomRun (atom false) (h 0+1))) :
    Nonempty (OracleTracePair q (sourceBlockWord s P atom (b+1) false)
      (sourceBlockWord s P atom (b+1) true) k
      (sourceClippingCost T n s b k ω a L+(SourceLeafCount T (b+1):ℝ)*E+sourceFitTail T n (b+1))
      (64*sourceSharpEnergyBudget T n s b R ω η a ((6*(2*k:ℕ):ℝ)*L))) ∧
    (∀j ≤ b+1,ω ≤ listTraceOverlap q hq
      (pureAtomRun (sourceBlockWord s P atom j false) (h j))
      (pureAtomRun (sourceBlockWord s P atom j false) (h j+1))) := by
  let := C.finiteOutcome
  have hov := source_nested_overlap hq C.error_nonneg s P h atom (C.hellinger hk) (b+1)
    hω hC hcount hpos hlift hsmall hbase
  refine ⟨?_,hov⟩
  have hm : C.first.expect (fun z => |C.score z|^(2*k)) ≤ L^(2*k) := by
    have H := C.first.expect_even_pow_le_of_moment C.score k hk (C.moment.trans hV)
    simpa only [pow_mul] using H
  exact actual_source_oracle hq C.error_nonneg s P T n h atom b R k H hTpos hP hn hT he hMotif hroot
    C.first C.second C.decode C.score C.density C.likelihood_nonneg C.first_simulation C.second_simulation
    ω a η L ha hL ⟨hω.1,lt_of_le_of_lt hω.2 (by norm_num)⟩
    (fun j hj => hov j (by omega)) hk hm hscale hη herror

/-- Conversion of a produced genuine oracle into the manuscript invariant.
 The scalar bounds here are exactly those to be discharged by scale margins. -/
def OracleTracePair.toConcrete {q E V N Δ d ω F : ℝ} {x y : List Bool} {k i h : ℕ}
    (C : OracleTracePair q x y k E V) (hq : q∈Set.Icc 0 1)
    (hlen : x.length=y.length) (hne : x≠y) (hlo : N/2 ≤ (x.length:ℝ))
    (hhi : (x.length:ℝ) ≤ N) (herror : E/(x.length:ℝ) ≤ ((i:ℝ)+1)*Δ)
    (hV : V ≤ N^(-d)) (hhlo : x.length ≤ h) (hhhi : (h:ℝ) ≤ F*(x.length:ℝ))
    (hov : ω ≤ listTraceOverlap q hq (pureAtomRun x h) (pureAtomRun x (h+1))) :
    ConcreteLevelPair q hq N Δ d ω F i k := {
  left := x
  right := y
  equalLength := hlen
  different := hne
  length_lower := hlo
  length_upper := hhi
  Outcome := C.Outcome
  finiteOutcome := C.finiteOutcome
  firstLaw := C.first
  secondLaw := C.second
  decode := C.decode
  error := E
  error_nonneg := C.error_nonneg
  normalized_error := herror
  first_simulation := C.first_simulation
  second_simulation := C.second_simulation
  score := C.score
  density := C.density
  score_bound := C.moment.trans hV
  overlapCount := h
  overlapCount_lower := hhlo
  overlapCount_upper := hhhi
  power_overlap := hov }

end TraceReconstruction

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
