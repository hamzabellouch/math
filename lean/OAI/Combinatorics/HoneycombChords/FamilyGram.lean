import OAI.Combinatorics.HoneycombChords.PositivePencils
import OAI.Combinatorics.HoneycombChords.NewtonKernel

namespace OAI

/-! Positive function families, Gram compression, basis changes, and knot continuity.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
noncomputable def zeroJetLift {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cons (-(∑ i,a i*cosineKernelJet (nodalOrder b (i.val+1)) 0 (b (i.val+1)) 0)) a
lemma zeroJetLift_eq {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (hb : b 0=0) (x : ℝ) :
    jetCombination b (zeroJetLift b a) x=zeroJetCombination b a x := by
  unfold jetCombination zeroJetLift zeroJetCombination zeroJet
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,Fin.val_zero,Fin.val_succ,jet_first_constant b hb,mul_one,mul_sub,sum_sub_distrib]
  ring
lemma zeroJetLift_ne_zero {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (ha : a ≠ 0) : zeroJetLift b a ≠ 0 := by
  intro h
  apply ha
  funext i
  exact congrFun h i.succ
lemma zeroJetCombination_zero {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) :
    zeroJetCombination b a 0=0 := by simp [zeroJetCombination,zeroJet]
lemma zeroJetCombination_continuous {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) :
    Continuous (zeroJetCombination b a) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((cosineKernelJet_contDiff_right _ _ _ 0).continuous.sub continuous_const)
lemma zeroJetCombination_zeros_card_lt {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ)
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hb0 : ∀ i : Fin (n+1),0 ≤ b i)
    (hfirst : b 0=0) (ha : a ≠ 0) (s : Finset ℝ)
    (hs : ∀ x∈s,0<x ∧ zeroJetCombination b a x=0) : s.card < n := by
  classical
  have h0 : (0:ℝ) ∉ s := fun h=>(lt_irrefl 0 (hs 0 h).1)
  have h:=jetCombination_zeros_card_lt b (zeroJetLift b a) hb hb0 (zeroJetLift_ne_zero b a ha) (insert 0 s) (by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · rw [zeroJetLift_eq b a hfirst,zeroJetCombination_zero];exact ⟨le_rfl,rfl⟩
    · exact ⟨(hs x hx).1.le,by rw [zeroJetLift_eq b a hfirst];exact (hs x hx).2⟩)
  rw [card_insert_of_notMem h0] at h
  omega
lemma zeroJetCombination_finite_zeros {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ)
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hb0 : ∀ i : Fin (n+1),0 ≤ b i)
    (hfirst : b 0=0) (ha : a ≠ 0) :
    {x : ℝ | 0<x ∧ zeroJetCombination b a x=0}.Finite := by
  apply (jetCombination_finite_zeros b (zeroJetLift b a) hb hb0 (zeroJetLift_ne_zero b a ha)).subset
  intro x hx
  exact ⟨hx.1.le,by rw [zeroJetLift_eq b a hfirst];exact hx.2⟩
noncomputable def zeroJetEvaluation {n : ℕ} (b : ℕ → ℝ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>zeroJet b i (x j)
lemma zeroJetEvaluation_det {n : ℕ} (b : ℕ → ℝ) (x : Fin n → ℝ) (hf : b 0=0) :
    (zeroJetEvaluation b x).det=(jetEvaluation b (Fin.cons 0 x)).det := by
  let B:=jetEvaluation b (Fin.cons 0 x)
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    .of (fun i j=>Fin.cases 1 (fun i=>zeroJet b i ((Fin.cons 0 x : Fin (n+1) → ℝ) j)) i)
  let c : Fin (n+1) → ℝ := Fin.cons 0 (fun i : Fin n=> -cosineKernelJet (nodalOrder b (i.val+1)) 0 (b (i.val+1)) 0)
  have he : A.det=B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c])
    intro i j
    refine Fin.cases ?_ (fun i=>?_) i
    · simp [A,B,c,jetEvaluation,jet_first_constant b hf]
    · simp only [A,B,c,Matrix.of_apply,Fin.cases_succ,Fin.cons_succ,jetEvaluation,Fin.val_succ,Fin.val_zero,jet_first_constant b hf,mul_one]
      dsimp [zeroJet]
      ring
  rw [Matrix.det_succ_column_zero,Fin.sum_univ_succ] at he
  have hsum : (∑ i : Fin n,(-1:ℝ)^(i.succ.val)*A i.succ 0*(A.submatrix i.succ.succAbove Fin.succ).det)=0 := by
    apply sum_eq_zero
    intro i _
    simp [A,zeroJet]
  rw [hsum,add_zero] at he
  have he' : (Matrix.of (fun i j : Fin n=>zeroJet b i (x j))).det=(jetEvaluation b (Fin.cons 0 x)).det := by
    simpa [A,B,Matrix.submatrix] using he
  rw [show Matrix.of (fun i j : Fin n=>zeroJet b i (x j))=zeroJetEvaluation b x from by ext i j;rfl] at he'
  exact he' 
lemma zeroJetEvaluation_det_pos {n : ℕ} (b : ℕ → ℝ) (x : Fin n → ℝ)
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hb0 : ∀ i : Fin (n+1),0 ≤ b i)
    (hf : b 0=0) (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
    0 < (zeroJetEvaluation b x).det := by
  rw [zeroJetEvaluation_det b x hf]
  apply jetEvaluation_det_pos b (Fin.cons 0 x) hb
  · intro i j
    refine Fin.cases ?_ (fun i=>?_) i
    · refine Fin.cases (fun h=>False.elim (lt_irrefl _ h)) (fun j _=>hx0 j) j
    · refine Fin.cases (fun h=>False.elim (Fin.not_lt_zero _ h)) (fun j h=>hx (Fin.succ_lt_succ_iff.mp h)) j
  · exact hb0
  · exact Fin.cases le_rfl (fun i=>(hx0 i).le)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv
/-- Positivity of the actual ordered evaluation determinant. Used below for
both regular and zero-at-origin jet bases, including the mixed second chain. -/
def PositiveEvaluation {n : ℕ} (F : Fin n → ℝ → ℝ) : Prop :=
  ∀ x : Fin n → ℝ,StrictMono x → (∀ i,0<x i) → 0<(evaluationMatrix F x).det
lemma evaluation_det_product_pos {n : ℕ} (F G : Fin n → ℝ → ℝ)
    (hF : PositiveEvaluation F) (hG : PositiveEvaluation G) (x : Fin n → ℝ)
    (hx : Function.Injective x) (hx0 : ∀ i,0<x i) :
    0<(evaluationMatrix F x).det*(evaluationMatrix G x).det := by
  obtain ⟨d,σ,hd,he⟩ := sorted_injective_real hx
  have hd0 i : 0<d i := by
    have h:=hx0 (σ.symm i)
    simpa only [he,Function.comp_apply,σ.apply_symm_apply] using h
  have hA:=hF d hd hd0
  have hB:=hG d hd hd0
  have hh (H : Fin n → ℝ → ℝ) : evaluationMatrix H x=(evaluationMatrix H d).submatrix id σ := by
    ext i j
    simp [evaluationMatrix,he]
  rw [hh F,hh G,Matrix.det_permute',Matrix.det_permute']
  have hs : (((Perm.sign σ:ℤ):ℝ))*(((Perm.sign σ:ℤ):ℝ))=1 := by
    rw [←Int.cast_mul,←Units.val_mul,Int.units_mul_self];norm_num
  nlinarith only [mul_pos hA hB,hs]
lemma evaluation_det_product_nonneg {n : ℕ} (F G : Fin n → ℝ → ℝ)
    (hF : PositiveEvaluation F) (hG : PositiveEvaluation G) (x : Fin n → ℝ)
    (hx0 : ∀ i,0<x i) : 0≤(evaluationMatrix F x).det*(evaluationMatrix G x).det := by
  by_cases hx : Function.Injective x
  · exact (evaluation_det_product_pos F G hF hG x hx hx0).le
  · obtain ⟨i,j,he,hij⟩ := Function.not_injective_iff.mp hx
    have hz : (evaluationMatrix F x).det=0 := by
      apply Matrix.det_zero_of_column_eq hij
      intro k
      simp only [evaluationMatrix,he]
    rw [hz,zero_mul]
lemma jet_positiveEvaluation {n : ℕ} (b : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hb0 : ∀ i : Fin n,0≤b i) :
    PositiveEvaluation (fun i : Fin n=>cosineKernelJet (nodalOrder b i) 0 (b i)) := by
  intro x hx hx0
  exact jetEvaluation_det_pos b x hb hx hb0 (fun i=>(hx0 i).le)
lemma zeroJet_positiveEvaluation {n : ℕ} (b : ℕ → ℝ)
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hb0 : ∀ i : Fin (n+1),0≤b i) (hfirst : b 0=0) :
    PositiveEvaluation (fun i : Fin n=>zeroJet b i) := by
  intro x hx hx0
  exact zeroJetEvaluation_det_pos b x hb hb0 hfirst hx hx0
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset Equiv MeasureTheory Filter
noncomputable def familyGram {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>∫ p in Set.Ioi (0:ℝ),F i (p^2)*
    G j (p^2)*w p
noncomputable def familyPointDensity {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ) (p : Fin n → ℝ) : ℝ :=
  (∏ i,w (p i))*(evaluationMatrix F (fun i=>(p i)^2)).det*(evaluationMatrix G (fun i=>(p i)^2)).det
lemma weighted_family_evaluation {n : ℕ} (w : ℝ → ℝ) (F : Fin n → ℝ → ℝ) (p : Fin n → ℝ) :
    (evaluationMatrix (fun i : Fin n=>fun q=>F i (q^2)*w q) p).det=
      (∏ i,w (p i))*(evaluationMatrix F (fun i=>(p i)^2)).det := by
  change (Matrix.of (fun i j : Fin n=>F i ((p j)^2)*w (p j))).det=_
  have he : Matrix.of (fun i j : Fin n=>F i ((p j)^2)*w (p j))=
      Matrix.of (fun i j : Fin n=>w (p j)*F i ((p j)^2)) := by
    ext i j
    exact mul_comm _ _
  rw [he]
  exact Matrix.det_mul_row (fun j=>w (p j)) (evaluationMatrix F (fun i=>(p i)^2))
lemma family_gram_andreief {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*
      G j (p^2)*w p) (Set.Ioi 0)) :
    Integrable (familyPointDensity (n:=n) w F G) (Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))) ∧
    (∫ p,familyPointDensity (n:=n) w F G p ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))))=
      Fintype.card (Perm (Fin n))*(familyGram (n:=n) w F G).det := by
  let FF : Fin n → ℝ → ℝ := fun i p=>F i (p^2)*w p
  let GG : Fin n → ℝ → ℝ := fun i p=>G i (p^2)
  have hFG i j : Integrable (fun p=>FF i p*GG j p) (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply (hi i j).congr
    filter_upwards with p
    dsimp [FF,GG]
    ring
  have he p : (evaluationMatrix FF p).det*(evaluationMatrix GG p).det=familyPointDensity w F G p := by
    rw [show (evaluationMatrix FF p).det=(∏ i,w (p i))*(evaluationMatrix F (fun i=>(p i)^2)).det from weighted_family_evaluation w F p]
    rfl
  have hgram : gramMatrix (volume.restrict (Set.Ioi (0:ℝ))) FF GG=familyGram w F G := by
    ext i j
    apply integral_congr_ae
    filter_upwards with p
    dsimp [FF,GG]
    ring
  constructor
  · simpa only [he] using integrable_det_evaluation_product _ FF GG hFG
  · simpa only [he,hgram] using andreief _ FF GG hFG
lemma familyPointDensity_pos {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ) (p : Fin n → ℝ)
    (hF : PositiveEvaluation F) (hG : PositiveEvaluation G)
    (hp : ∀ i,0<p i) (hw : ∀ q,0<q → 0<w q) (hpi : Function.Injective p) :
    0 < familyPointDensity w F G p := by
  have hin : Function.Injective (fun i=>(p i)^2) := by
    intro i j hij
    apply hpi
    exact (sq_eq_sq₀ (hp i).le (hp j).le).mp hij
  rw [familyPointDensity,mul_assoc]
  exact mul_pos (prod_pos (fun i _=>hw _ (hp i)))
    (evaluation_det_product_pos F G hF hG _ hin (fun i=>sq_pos_of_pos (hp i)))
lemma familyGram_det_pos {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (hF : PositiveEvaluation F) (hG : PositiveEvaluation G) (hw : ∀ q,0<q → 0<w q)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>F i (p^2)*
      G j (p^2)*w p) (Set.Ioi 0)) :
    0 < (familyGram (n:=n) w F G).det := by
  let μ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))
  obtain ⟨hI,hA⟩ := family_gram_andreief w F G hi
  have hae : ∀ᵐ p ∂μ,∀ i,0<p i := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) (i:=i)).eventually (ae_restrict_mem measurableSet_Ioi)
  have hnn : 0 ≤ᵐ[μ] familyPointDensity w F G := by
    filter_upwards [hae] with p hp
    dsimp only [Pi.zero_apply]
    rw [familyPointDensity,mul_assoc]
    exact mul_nonneg (prod_nonneg (fun i _=>(hw _ (hp i)).le))
      (evaluation_det_product_nonneg F G hF hG _ (fun i=>sq_pos_of_pos (hp i)))
  let box : Set (Fin n → ℝ) := Set.pi Set.univ (fun i=>Set.Ioo ((i:ℝ)+1) ((i:ℝ)+3/2))
  have hbox : box ⊆ Function.support (familyPointDensity w F G) := by
    intro p hp
    have hp' (i : Fin n) : (i:ℝ)+1<p i ∧ p i<(i:ℝ)+3/2 := hp i (Set.mem_univ _)
    have hp0 i : 0<p i := by have hn : (0:ℝ) ≤ i := Nat.cast_nonneg _;linarith [(hp' i).1]
    have hmono : StrictMono p := by
      intro i j hij
      have hnat : i.val+1 ≤ j.val := hij
      have hreal : (i:ℝ)+1 ≤ j := by exact_mod_cast hnat
      linarith [(hp' i).2,(hp' j).1]
    exact (familyPointDensity_pos w F G p hF hG hp0 hw hmono.injective).ne'
  have hboxpos : 0<μ box := by
    change 0<Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) (Set.pi Set.univ _)
    rw [Measure.pi_pi]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply ne_of_gt
    rw [Measure.restrict_apply measurableSet_Ioo,Set.inter_eq_left.mpr,Real.volume_Ioo]
    · exact ENNReal.ofReal_pos.mpr (by norm_num)
    · intro p hp
      have hn : (0:ℝ) ≤ i := Nat.cast_nonneg _
      exact lt_trans (by linarith) hp.1
  have hpos : 0<∫ p,familyPointDensity w F G p ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hnn hI).mpr (hboxpos.trans_le (measure_mono hbox))
  rw [hA] at hpos
  exact (mul_pos_iff.mp hpos).elim (fun h=>h.2) (fun h=>False.elim (not_lt_of_ge (Nat.cast_nonneg _) h.1))
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
/-- Quadratic-form bounds give determinant bounds with the exact dimension.
This is the finite-dimensional stability estimate required in the polynomial
compression step of strip-asymptotics.tex:83--84. -/
theorem determinant_quotient_of_quadratic_bounds {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA:A.IsHermitian) (hB:B.PosDef)
    {l u:ℝ} (hl:0≤l)
    (hlo:∀ v:Fin n→ℝ,l*(v ⬝ᵥ (B *ᵥ v))≤v ⬝ᵥ (A *ᵥ v))
    (hup:∀ v:Fin n→ℝ,v ⬝ᵥ (A *ᵥ v)≤u*(v ⬝ᵥ (B *ᵥ v))) :
    l^n≤A.det/B.det ∧ A.det/B.det≤u^n := by
  obtain ⟨P,e,hP,hPB,hPA⟩:=positive_pencil_normal_form A B hA hB
  have hquad (T:Matrix (Fin n) (Fin n) ℝ) (v:Fin n→ℝ) :
      (P *ᵥ v) ⬝ᵥ (T *ᵥ (P *ᵥ v))=v ⬝ᵥ ((Pᴴ*T*P) *ᵥ v) := by
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial,←mulVec_mulVec]
    exact (dotProduct_comm _ _).trans (Matrix.dotProduct_transpose_mulVec P v (T *ᵥ (P *ᵥ v))).symm
  have he (i:Fin n):l≤e i ∧ e i≤u := by
    have ha:=hlo (P *ᵥ Pi.single i 1)
    have hb:=hup (P *ᵥ Pi.single i 1)
    rw [hquad,hquad,hPB,hPA] at ha hb
    simpa [Matrix.mulVec_diagonal] using And.intro ha hb
  have hdA:=congrArg Matrix.det hPA
  have hdB:=congrArg Matrix.det hPB
  simp only [Matrix.det_mul,Matrix.det_conjTranspose,star_trivial,Matrix.det_diagonal,Matrix.det_one] at hdA hdB
  have hratio:A.det/B.det=∏ i,e i := by
    apply (div_eq_iff hB.det_pos.ne').mpr
    nlinarith [congrArg (fun x:ℝ=>x*B.det) hdA,congrArg (fun x:ℝ=>x*A.det) hdB]
  rw [hratio]
  constructor
  · calc
      l^n=∏ _i:Fin n,l := by simp
      _≤∏ i,e i:=prod_le_prod₀ (fun _ _=>hl) (fun i _=>(he i).1)
  · calc
      (∏ i,e i)≤∏ _i:Fin n,u:=prod_le_prod₀ (fun i _=>hl.trans (he i).1) (fun i _=>(he i).2)
      _=u^n := by simp
/-- Loewner monotonicity of determinant, with a positive definite base. -/
theorem determinant_mono_of_positive_base {n:ℕ}
    (A B:Matrix (Fin n) (Fin n) ℝ) (hA:A.IsHermitian) (hB:B.PosDef)
    (h:∀ v:Fin n→ℝ,v ⬝ᵥ (B *ᵥ v)≤v ⬝ᵥ (A *ᵥ v)) : B.det≤A.det := by
  obtain ⟨P,e,hP,hPB,hPA⟩:=positive_pencil_normal_form A B hA hB
  have hlo:∀ v:Fin n→ℝ,(1:ℝ)*(v ⬝ᵥ (B *ᵥ v))≤v ⬝ᵥ (A *ᵥ v) := by simpa using h
  have hn:A.det/B.det≥1 := by
    have he (i:Fin n):1≤e i := by
      have hh:=h (P *ᵥ Pi.single i 1)
      have hquad (T:Matrix (Fin n) (Fin n) ℝ) (v:Fin n→ℝ) :
          (P *ᵥ v) ⬝ᵥ (T *ᵥ (P *ᵥ v))=v ⬝ᵥ ((Pᴴ*T*P) *ᵥ v) := by
        simp only [Matrix.conjTranspose_eq_transpose_of_trivial,←mulVec_mulVec]
        exact (dotProduct_comm _ _).trans (Matrix.dotProduct_transpose_mulVec P v (T *ᵥ (P *ᵥ v))).symm
      rw [hquad,hquad,hPB,hPA] at hh
      simpa [Matrix.mulVec_diagonal] using hh
    have ha:=congrArg Matrix.det hPA
    have hb:=congrArg Matrix.det hPB
    simp only [det_mul,det_conjTranspose,star_trivial,det_diagonal,det_one] at ha hb
    have heprod:(1:ℝ)≤∏ i,e i := by
      calc
        1=∏ _i:Fin n,(1:ℝ) := by simp
        _≤∏ i,e i:=prod_le_prod₀ (by intro i _;norm_num) (fun i _=>he i)
    apply (le_div_iff₀ hB.det_pos).mpr
    have hp:0≤B.det:=hB.det_pos.le
    nlinarith [congrArg (fun x:ℝ=>x*B.det) ha,congrArg (fun x:ℝ=>x*A.det) hb,mul_le_mul_of_nonneg_right heprod hp]
  simpa only [one_mul] using (le_div_iff₀ hB.det_pos).mp hn
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix
lemma small_error_power_bounds {n:ℕ} {η:ℝ} (hη:0≤η) (hη1:η≤1/2)
    (hn:(n:ℝ)*η≤1/2) :
    (1:ℝ)/2≤(1-η)^n ∧ (1+η)^n≤2 := by
  have hl:(1:ℝ)/2≤(1-η)^n := by
    have h:=one_add_mul_le_pow (a:= -η) (by linarith : (-2:ℝ)≤-η) n
    simp only [mul_neg,←sub_eq_add_neg] at h
    linarith
  refine ⟨hl,?_⟩
  have hm:(1+η)^n*(1-η)^n≤1 := by
    rw [←mul_pow]
    apply pow_le_one₀ (by nlinarith) (by nlinarith [sq_nonneg η])
  have hp:0≤(1+η)^n:=pow_nonneg (by linarith) _
  nlinarith [mul_le_mul_of_nonneg_left hl hp]
/-- Uniform constant-factor determinant stability requires dimension times
quadratic error to be small; this factor cannot be omitted. -/
theorem determinant_small_relative_error {n:ℕ}
    (A D:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (hD:D.IsHermitian)
    {η:ℝ} (hη:0≤η) (hη1:η≤1/2) (hn:(n:ℝ)*η≤1/2)
    (herr:∀ v:Fin n→ℝ,|v ⬝ᵥ (D *ᵥ v)-v ⬝ᵥ (A *ᵥ v)|≤η*(v ⬝ᵥ (A *ᵥ v))) :
    (1:ℝ)/2≤D.det/A.det ∧ D.det/A.det≤2 := by
  have hh:=determinant_quotient_of_quadratic_bounds D A hD hA (l:=1-η) (u:=1+η)
    (show 0≤1-η by linarith)
    (by intro v;have h:=(abs_le.mp (herr v)).1; linarith)
    (by intro v;have h:=(abs_le.mp (herr v)).2; linarith)
  have hp:=small_error_power_bounds hη hη1 hn
  exact ⟨hp.1.trans hh.1,hh.2.trans hp.2⟩

theorem gram_quotient_small_relative_error {n:ℕ}
    (A B D E:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (hB:B.PosDef)
    (hD:D.IsHermitian) (hE:E.IsHermitian)
    {η:ℝ} (hη:0≤η) (hη1:η≤1/2) (hn:(n:ℝ)*η≤1/2)
    (hAD:∀ v:Fin n→ℝ,|v ⬝ᵥ (D *ᵥ v)-v ⬝ᵥ (A *ᵥ v)|≤η*(v ⬝ᵥ (A *ᵥ v)))
    (hBE:∀ v:Fin n→ℝ,|v ⬝ᵥ (E *ᵥ v)-v ⬝ᵥ (B *ᵥ v)|≤η*(v ⬝ᵥ (B *ᵥ v))) :
    (A.det/B.det)/4≤D.det/E.det ∧ D.det/E.det≤4*(A.det/B.det) := by
  obtain ⟨hlD,huD⟩:=determinant_small_relative_error A D hA hD hη hη1 hn hAD
  obtain ⟨hlE,huE⟩:=determinant_small_relative_error B E hB hE hη hη1 hn hBE
  have hlD':A.det/2≤D.det:=by
    have h:=(le_div_iff₀ hA.det_pos).mp hlD
    linarith
  have huD':D.det≤2*A.det:=(div_le_iff₀ hA.det_pos).mp huD
  have hlE':B.det/2≤E.det:=by
    have h:=(le_div_iff₀ hB.det_pos).mp hlE
    linarith
  have huE':E.det≤2*B.det:=(div_le_iff₀ hB.det_pos).mp huE
  have hEpos:0<E.det:=lt_of_lt_of_le (half_pos hB.det_pos) hlE'
  constructor
  · apply (le_div_iff₀ hEpos).mpr
    have hcross:D.det*B.det≥A.det*E.det/4 := by
      have h1:=mul_le_mul_of_nonneg_right hlD' hB.det_pos.le
      have h2:=mul_le_mul_of_nonneg_left huE' hA.det_pos.le
      nlinarith
    calc
      (A.det/B.det/4)*E.det=(A.det*E.det/4)/B.det := by ring
      _≤D.det := (div_le_iff₀ hB.det_pos).mpr hcross
  · apply (div_le_iff₀ hEpos).mpr
    have hcross:D.det*B.det≤4*A.det*E.det := by
      have h1:=mul_le_mul_of_nonneg_right huD' hB.det_pos.le
      have h2:=mul_le_mul_of_nonneg_left hlE' hA.det_pos.le
      nlinarith
    calc
      D.det≤(4*A.det*E.det)/B.det := (le_div_iff₀ hB.det_pos).mpr hcross
      _=4*(A.det/B.det)*E.det := by ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open MeasureTheory Matrix Finset Equiv

lemma rectangular_diagonal_gram_det {n m:ℕ} (C:Matrix (Fin n) (Fin m) ℝ) (e:Fin m→ℝ) :
    (Fintype.card (Perm (Fin n)):ℝ)*(C*diagonal e*Cᵀ).det=
      ∑ f:Fin n→Fin m,(∏ i,e (f i))*(C.submatrix id f).det^2 := by
  let F:Fin n→Fin m→ℝ:=fun i j=>e j*C i j
  let G:Fin n→Fin m→ℝ:=C
  have hi i j:Integrable (fun k=>F i k*G j k) (Measure.count:Measure (Fin m)) := by
    exact integrable_count_iff.mpr (by exact (hasSum_fintype _).summable)
  have h:=andreief (Measure.count:Measure (Fin m)) F G hi
  have hg:gramMatrix (Measure.count:Measure (Fin m)) F G=C*diagonal e*Cᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [gramMatrix,integral_count,Matrix.mul_diagonal,Matrix.transpose_apply]
    apply sum_congr rfl
    intro k _
    dsimp [F,G]
    ring
  have he (f:Fin n→Fin m):(evaluationMatrix F f).det*(evaluationMatrix G f).det=
      (∏ i,e (f i))*(C.submatrix id f).det^2 := by
    have hf:evaluationMatrix F f=Matrix.of (fun i j=>e (f j)*(C.submatrix id f) i j) := rfl
    rw [hf,Matrix.det_mul_row]
    change (∏ i,e (f i))*(C.submatrix id f).det*(C.submatrix id f).det=_
    ring
  rw [integral_fintype (integrable_det_evaluation_product _ F G hi),hg] at h
  simp only [Measure.real,Measure.pi_singleton,Measure.count_singleton,prod_const_one,ENNReal.toReal_one,one_smul,he] at h
  exact h.symm
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv
lemma diagonal_compression_det_lower {n m:ℕ} (C:Matrix (Fin n) (Fin m) ℝ) (e:Fin m→ℝ)
    (he:∀ i,0≤e i) (he1:∀ i,e i≤1) :
    (∏ i,e i)*(C*Cᵀ).det≤(C*diagonal e*Cᵀ).det := by
  have hn:0<(Fintype.card (Perm (Fin n)):ℝ):=by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hn).mp
  have hbase:=rectangular_diagonal_gram_det C (fun _=>1)
  simp only [Matrix.diagonal_one,Matrix.mul_one,prod_const_one,one_mul] at hbase
  have hweight:=rectangular_diagonal_gram_det C e
  calc
    (Fintype.card (Perm (Fin n)):ℝ)*((∏ i,e i)*(C*Cᵀ).det)=
      (∏ i,e i)*((Fintype.card (Perm (Fin n)):ℝ)*(C*Cᵀ).det) := by ring
    _=(∏ i,e i)*(∑ f:Fin n→Fin m,(C.submatrix id f).det^2) := by rw [hbase]
    _≤∑ f:Fin n→Fin m,(∏ i,e (f i))*(C.submatrix id f).det^2 := by
      rw [mul_sum]
      apply sum_le_sum
      intro f _
      by_cases hf:Function.Injective f
      · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hp:(∏ i:Fin m,e i)≤∏ i∈univ.image f,e i:=
          prod_le_prod_of_subset_of_le_one₀ (subset_univ _) (fun i _=>he i) (fun i _ _=>he1 i)
        rw [prod_image (fun i _ j _ hij=>hf hij)] at hp
        exact hp
      · obtain ⟨i,j,hij,heq⟩:=Function.not_injective_iff.mp hf
        have hz:(C.submatrix id f).det=0:=Matrix.det_zero_of_column_eq heq (fun k=>by simp [hij])
        simp [hz]
    _=(Fintype.card (Perm (Fin n)):ℝ)*(C*diagonal e*Cᵀ).det := hweight.symm
/-- Compression to any finite subspace increases the determinant of a positive
contraction. The Gram quotient makes the statement independent of the basis. -/
theorem positive_contraction_compression {n m:ℕ}
    (A B:Matrix (Fin m) (Fin m) ℝ) (C:Matrix (Fin n) (Fin m) ℝ)
    (hA:A.PosDef) (hB:B.PosDef) (hCB:(C*B*Cᵀ).PosDef)
    (hAB:∀ v:Fin m→ℝ,v ⬝ᵥ (A *ᵥ v)≤v ⬝ᵥ (B *ᵥ v)) :
    A.det/B.det≤(C*A*Cᵀ).det/(C*B*Cᵀ).det := by
  obtain ⟨P,e,hP,hPB,hPA⟩:=positive_pencil_normal_form A B hA.1 hB
  have hPP:P*P⁻¹=1:=Matrix.mul_nonsing_inv P hP
  have hPP':P⁻¹*P=1:=Matrix.nonsing_inv_mul P hP
  have hPT:Pᵀ*P⁻¹ᵀ=1:=by rw [←Matrix.transpose_mul,hPP',Matrix.transpose_one]
  have he:∀ i,0<e i := by
    have hc:=hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (P.isUnit_iff_isUnit_det.mpr hP))
    rw [hPA] at hc
    intro i
    simpa using (hc.diag_pos (i:=i))
  have he1 (i:Fin m):e i≤1 := by
    have hh:=hAB (P *ᵥ Pi.single i 1)
    have hquad (T:Matrix (Fin m) (Fin m) ℝ) (v:Fin m→ℝ) :
        (P *ᵥ v) ⬝ᵥ (T *ᵥ (P *ᵥ v))=v ⬝ᵥ ((Pᴴ*T*P) *ᵥ v) := by
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial,←mulVec_mulVec]
      exact (dotProduct_comm _ _).trans (Matrix.dotProduct_transpose_mulVec P v (T *ᵥ (P *ᵥ v))).symm
    rw [hquad,hquad,hPA,hPB] at hh
    simpa [Matrix.mulVec_diagonal] using hh
  have hnormal (T U:Matrix (Fin m) (Fin m) ℝ) (h:Pᴴ*T*P=U) : T=P⁻¹ᵀ*U*P⁻¹ := by
    have hl:P⁻¹ᵀ*Pᵀ=1:=by rw [←Matrix.transpose_mul,hPP,Matrix.transpose_one]
    rw [←h,Matrix.conjTranspose_eq_transpose_of_trivial]
    calc
      T=(P⁻¹ᵀ*Pᵀ)*T*(P*P⁻¹) := by rw [hl,hPP];simp
      _=P⁻¹ᵀ*(Pᵀ*T*P)*P⁻¹ := by simp only [Matrix.mul_assoc]
  let D:Matrix (Fin n) (Fin m) ℝ:=C*P⁻¹ᵀ
  have hDA:C*A*Cᵀ=D*diagonal e*Dᵀ := by
    rw [hnormal A _ hPA]
    dsimp [D]
    rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  have hDB:C*B*Cᵀ=D*Dᵀ := by
    rw [hnormal B _ hPB]
    dsimp [D]
    rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc,Matrix.one_mul]
  have hr:A.det/B.det=∏ i,e i := by
    have ha:=congrArg Matrix.det hPA
    have hb:=congrArg Matrix.det hPB
    simp only [det_mul,det_conjTranspose,star_trivial,det_diagonal,det_one] at ha hb
    apply (div_eq_iff hB.det_pos.ne').mpr
    nlinarith [congrArg (fun x:ℝ=>x*B.det) ha,congrArg (fun x:ℝ=>x*A.det) hb]
  apply (le_div_iff₀ hCB.det_pos).mpr
  rw [hr,hDA,hDB]
  exact diagonal_compression_det_lower D e (fun i=>(he i).le) he1
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
noncomputable def finiteFamilyCombination {n:ℕ} (F:Fin n→ℝ→ℝ) (v:Fin n→ℝ) (x:ℝ):ℝ:=∑ i,v i*F i x
noncomputable def familySquaredNorm (w f:ℝ→ℝ):ℝ:=∫ p in Set.Ioi 0,f (p^2)^2*w p
lemma finiteFamilyCombination_pair_integrable {n m:ℕ} (w:ℝ→ℝ) (F:Fin n→ℝ→ℝ) (G:Fin m→ℝ→ℝ)
    (hi:∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (a:Fin n→ℝ) (b:Fin m→ℝ) :
    IntegrableOn (fun p=>finiteFamilyCombination F a (p^2)*finiteFamilyCombination G b (p^2)*w p) (Set.Ioi 0) := by
  have he p:finiteFamilyCombination F a (p^2)*finiteFamilyCombination G b (p^2)*w p=
      ∑ i,∑ j,a i*b j*(F i (p^2)*G j (p^2)*w p) := by
    simp only [finiteFamilyCombination,sum_mul,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>(hi i j).const_mul _))
lemma familyGram_congruence {n m:ℕ} (w:ℝ→ℝ) (F:Fin n→ℝ→ℝ)
    (hi:∀ i j,IntegrableOn (fun p=>F i (p^2)*F j (p^2)*w p) (Set.Ioi 0))
    (C:Matrix (Fin m) (Fin n) ℝ) :
    familyGram w (fun i=>finiteFamilyCombination F (C i)) (fun i=>finiteFamilyCombination F (C i))=
      C*familyGram w F F*Cᵀ := by
  ext i j
  have hp k l:IntegrableOn (fun p=>C i k*C j l*(F k (p^2)*F l (p^2)*w p)) (Set.Ioi 0):=(hi k l).const_mul _
  have he p:finiteFamilyCombination F (C i) (p^2)*finiteFamilyCombination F (C j) (p^2)*w p=
      ∑ k,∑ l,C i k*C j l*(F k (p^2)*F l (p^2)*w p) := by
    simp only [finiteFamilyCombination,sum_mul,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro l _
    ring
  simp only [familyGram,he]
  rw [integral_finsetSum _ (fun k _=>integrable_finsetSum _ (fun l _=>hp k l))]
  simp_rw [integral_finsetSum _ (fun l _=>hp _ l),integral_const_mul]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,sum_mul,familyGram]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro l _
  ring
lemma familyGram_quad {n:ℕ} (w:ℝ→ℝ) (F:Fin n→ℝ→ℝ)
    (hi:∀ i j,IntegrableOn (fun p=>F i (p^2)*F j (p^2)*w p) (Set.Ioi 0))
    (v:Fin n→ℝ) :
    v ⬝ᵥ (familyGram w F F *ᵥ v)=familySquaredNorm w (finiteFamilyCombination F v) := by
  have h:=congrArg (fun A:Matrix (Fin 1) (Fin 1) ℝ=>A 0 0)
    (familyGram_congruence w F hi (Matrix.of fun (_:Fin 1) i=>v i))
  simp only [familyGram,Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply] at h
  change (∫ p in Set.Ioi 0, finiteFamilyCombination F v (p^2) * finiteFamilyCombination F v (p^2) * w p) = _ at h
  unfold familySquaredNorm
  simp_rw [show ∀ a:ℝ, a^2=a*a from fun a=>pow_two a]
  rw [show (fun p => finiteFamilyCombination F v (p*p)*finiteFamilyCombination F v (p*p)*w p) = (fun p => finiteFamilyCombination F v (p^2)*finiteFamilyCombination F v (p^2)*w p) by simp only [pow_two]]
  rw [h]
  simp only [dotProduct,Matrix.mulVec,mul_sum,sum_mul,familyGram]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring
lemma familyGram_hermitian {n:ℕ} (w:ℝ→ℝ) (F:Fin n→ℝ→ℝ) : (familyGram w F F).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [familyGram,star_trivial]
  apply integral_congr_ae
  filter_upwards with p
  ring
lemma familySquaredNorm_nonneg (w f:ℝ→ℝ) (hw:∀ p,0<p→0≤w p) : 0≤familySquaredNorm w f := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact mul_nonneg (sq_nonneg _) (hw p hp)
lemma familySquaredNorm_error_bound {n:ℕ} (w:ℝ→ℝ) (E:Fin n→ℝ→ℝ)
    (hw:∀ p,0<p→0≤w p)
    (hi:∀ i j,IntegrableOn (fun p=>E i (p^2)*E j (p^2)*w p) (Set.Ioi 0))
    {δ:ℝ} (hE:∀ i,familySquaredNorm w (E i)≤δ) (v:Fin n→ℝ) :
    familySquaredNorm w (finiteFamilyCombination E v)≤((n:ℝ)*δ)*(∑ i,v i^2) := by
  have hcomb:=finiteFamilyCombination_pair_integrable w E E hi v v
  have hsq:IntegrableOn (fun p=>finiteFamilyCombination E v (p^2)^2*w p) (Set.Ioi 0):=by simpa only [pow_two] using hcomb
  have hdiag i:IntegrableOn (fun p=>(E i (p^2))^2*w p) (Set.Ioi 0):=by simpa only [pow_two] using hi i i
  have hsum:IntegrableOn (fun p=>(∑ i,v i^2)*(∑ i,E i (p^2)^2*w p)) (Set.Ioi 0):=
    (integrable_finsetSum _ fun i _=>hdiag i).const_mul _
  have hm:familySquaredNorm w (finiteFamilyCombination E v)≤
      (∑ i,v i^2)*(∑ i,familySquaredNorm w (E i)) := by
    unfold familySquaredNorm
    rw [←integral_finsetSum _ (fun i _=>hdiag i),←integral_const_mul]
    apply integral_mono_ae hsq hsum
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hs:=Finset.sum_mul_sq_le_sq_mul_sq univ v (fun i=>E i (p^2))
    have hh:=mul_le_mul_of_nonneg_right hs (hw p hp)
    simpa only [finiteFamilyCombination,mul_sum,sum_mul,mul_assoc] using hh
  have htotal:(∑ i,familySquaredNorm w (E i))≤(n:ℝ)*δ:=by
    calc
      _≤∑ _i:Fin n,δ:=sum_le_sum (fun i _=>hE i)
      _=(n:ℝ)*δ:=by simp
  calc
    _≤(∑ i,v i^2)*(∑ i,familySquaredNorm w (E i)):=hm
    _≤(∑ i,v i^2)*((n:ℝ)*δ):=mul_le_mul_of_nonneg_left htotal (sum_nonneg (fun i _=>sq_nonneg _))
    _=_:=by ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Equiv Filter

/-- Evaluation rows with the rank-one interpolation correction. -/
noncomputable def residualFamily {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ) (a : ℝ) :
    Fin n → ℝ → ℝ := fun i x=>F i x-F i a*H x/H a
noncomputable def meanResidualRatio {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a : ℝ) : ℝ :=
    (familyGram w (residualFamily F H a) G).det/(familyGram w F G).det

lemma residualFamily_pair_integrable {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a : ℝ)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p=>H (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    ∀ i j,IntegrableOn (fun p=>residualFamily F H a i (p^2)*G j (p^2)*w p) (Set.Ioi 0) := by
  intro i j
  convert (hi i j).sub ((hH j).const_mul (F i a/H a)) using 1
  funext p
  simp only [residualFamily, Pi.sub_apply]
  ring

lemma residualFamily_gram {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a : ℝ)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p=>H (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    familyGram w (residualFamily F H a) G=familyGram w F G-
      vecMulVec (fun i=>F i a/H a) (fun j=>∫ p in Set.Ioi 0,H (p^2)*G j (p^2)*w p) := by
  ext i j
  have he : (fun p=>residualFamily F H a i (p^2)*G j (p^2)*w p)=
      (fun p=>F i (p^2)*G j (p^2)*w p-(F i a/H a)*(H (p^2)*G j (p^2)*w p)) := by
    funext p
    simp only [residualFamily]
    ring
  change (∫ p in Set.Ioi 0,residualFamily F H a i (p^2)*G j (p^2)*w p)=_
  rw [he,integral_sub (hi i j) ((hH j).const_mul _),integral_const_mul]
  rfl

lemma det_sub_vecMulVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.det≠0)
    (u v : Fin n → ℝ) :
    (A-vecMulVec u v).det=A.det*(1-v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
  have he : A-vecMulVec u v=A+replicateCol Unit (-u)*replicateRow Unit v := by
    rw [←vecMulVec_eq]
    ext i j
    simp [sub_eq_add_neg]
  rw [he,det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hA),
    Matrix.mul_assoc,←replicateCol_mulVec]
  congr 1
  rw [det_unique]
  simp only [Matrix.add_apply,Matrix.one_apply_eq,replicateRow_mul_replicateCol_apply,
    mulVec_neg,dotProduct_neg,←sub_eq_add_neg]

lemma meanResidualRatio_formula {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a : ℝ)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p=>H (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hd : (familyGram w F G).det≠0) :
    meanResidualRatio w F G H a=1-
      (fun j=>∫ p in Set.Ioi 0,H (p^2)*G j (p^2)*w p) ⬝ᵥ
      ((familyGram w F G)⁻¹ *ᵥ (fun i=>F i a/H a)) := by
  rw [meanResidualRatio,residualFamily_gram w F G H a hi hH,det_sub_vecMulVec hd]
  exact mul_div_cancel_left₀ _ hd


lemma meanResidualRatio_eq_integral {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a : ℝ)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p=>H (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    meanResidualRatio w F G H a=
      (∫ p,familyPointDensity w (residualFamily F H a) G p
        ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))) /
      (∫ p,familyPointDensity w F G p
        ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))) := by
  rw [(family_gram_andreief w F G hi).2,
    (family_gram_andreief w (residualFamily F H a) G (residualFamily_pair_integrable w F G H a hi hH)).2]
  exact (mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm

lemma familyPointDensity_tilt {n : ℕ} (w r : ℝ → ℝ) (F G : Fin n → ℝ → ℝ) (p : Fin n → ℝ) :
    familyPointDensity (fun x=>r x*w x) F G p=
      (∏ i,r (p i))*familyPointDensity w F G p := by
  simp only [familyPointDensity,prod_mul_distrib]
  ring

/-- Transfer any pointwise residual bound to the exact determinant averages. -/
lemma meanResidualRatio_bound {n : ℕ} (w w₁ w₂ : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a A B : ℝ)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hi₁ : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w₁ p) (Set.Ioi 0))
    (hi₂ : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w₂ p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p=>H (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hd : 0<(familyGram w F G).det)
    (hb : ∀ p : Fin n → ℝ,(∀ i,0<p i) →
      familyPointDensity w (residualFamily F H a) G p ≤
        A*familyPointDensity w₁ F G p+B*familyPointDensity w₂ F G p) :
    meanResidualRatio w F G H a ≤
      A*((familyGram w₁ F G).det/(familyGram w F G).det)+
        B*((familyGram w₂ F G).det/(familyGram w F G).det) := by
  let μ:=Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))
  have hae : ∀ᵐ p ∂μ,∀ i,0<p i := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) (i:=i)).eventually (ae_restrict_mem measurableSet_Ioi)
  have hR:=family_gram_andreief w (residualFamily F H a) G (residualFamily_pair_integrable w F G H a hi hH)
  have h₁:=family_gram_andreief w₁ F G hi₁
  have h₂:=family_gram_andreief w₂ F G hi₂
  have hI:=integral_mono_ae hR.1 ((h₁.1.const_mul A).add (h₂.1.const_mul B)) (hae.mono hb)
  simp only [Pi.add_apply] at hI
  rw [integral_add (h₁.1.const_mul A) (h₂.1.const_mul B),integral_const_mul,integral_const_mul,
    hR.2,h₁.2,h₂.2] at hI
  have hc : (0:ℝ)<Fintype.card (Perm (Fin n)) := Nat.cast_pos.mpr Fintype.card_pos
  have hI' : (familyGram w (residualFamily F H a) G).det ≤
      A*(familyGram w₁ F G).det+B*(familyGram w₂ F G).det := by nlinarith
  rw [meanResidualRatio]
  apply (div_le_iff₀ hd).mpr
  have he : (A * ((familyGram w₁ F G).det / (familyGram w F G).det) +
      B * ((familyGram w₂ F G).det / (familyGram w F G).det)) * (familyGram w F G).det =
      A*(familyGram w₁ F G).det+B*(familyGram w₂ F G).det := by
    field_simp [hd.ne']
  rw [he]
  exact hI'

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix Filter Topology MeasureTheory

lemma newton_pair_integrable {b c : ℕ → ℝ} {R S : ℝ} (hb : ∀ i,0 ≤ b i ∧ b i≤R)
    (hc : ∀ i,0 ≤ c i ∧ c i≤S) (w : ℝ → ℝ) (hw : Measurable w)
    (hw0 : ∀ p,0<p → 0≤w p) (r s : ℕ)
    (hi : IntegrableOn (fun p ↦ cosineKernelJet r 0 R (p^2)*cosineKernelJet s 0 S (p^2)*w p) (Set.Ioi 0)) :
    IntegrableOn (fun p ↦ newtonKernel b (p^2) 0 r*newtonKernel c (p^2) 0 s*w p) (Set.Ioi 0) := by
  have hR : 0 ≤ R := (hb 0).1.trans (hb 0).2
  have hS : 0 ≤ S := (hc 0).1.trans (hc 0).2
  apply hi.mono'
  · exact ((((continuous_newtonKernel (R:=R+1) (by linarith)
      (fun i ↦ by rw [abs_of_nonneg (hb i).1]; linarith [(hb i).2]) r).comp (continuous_id.pow 2)).measurable.mul
      (((continuous_newtonKernel (R:=S+1) (by linarith)
        (fun i ↦ by rw [abs_of_nonneg (hc i).1]; linarith [(hc i).2]) s).comp (continuous_id.pow 2)).measurable)).mul hw).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hnb:=newtonKernel_nonneg (fun i ↦ (hb i).1) (sq_nonneg p) r
    have hnc:=newtonKernel_nonneg (fun i ↦ (hc i).1) (sq_nonneg p) s
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hnb hnc) (hw0 p hp))]
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (newtonKernel_le_jet (fun i ↦ (hb i).1) (fun i ↦ (hb i).2) (sq_nonneg p) r)
      (newtonKernel_le_jet (fun i ↦ (hc i).1) (fun i ↦ (hc i).2) (sq_nonneg p) s)
      hnc (cosineKernelJet_nonneg hR (sq_nonneg p) r 0)) (hw0 p hp)

lemma tendsto_newton_pair_integral {b c : ℕ → ℕ → ℝ} {B C : ℕ → ℝ} {R S : ℝ}
    (hb : ∀ k i,0 ≤ b k i ∧ b k i≤R) (hc : ∀ k i,0 ≤ c k i ∧ c k i≤S)
    (hB : ∀ i,0 ≤ B i ∧ B i≤R) (hC : ∀ i,0 ≤ C i ∧ C i≤S)
    (htb : Tendsto b atTop (𝓝 B)) (htc : Tendsto c atTop (𝓝 C))
    (w : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀ p,0<p → 0≤w p) (r s : ℕ)
    (hi : IntegrableOn (fun p ↦ cosineKernelJet r 0 R (p^2)*cosineKernelJet s 0 S (p^2)*w p) (Set.Ioi 0)) :
    Tendsto (fun k ↦ ∫ p in Set.Ioi 0,newtonKernel (b k) (p^2) 0 r*newtonKernel (c k) (p^2) 0 s*w p)
      atTop (𝓝 (∫ p in Set.Ioi 0,newtonKernel B (p^2) 0 r*newtonKernel C (p^2) 0 s*w p)) := by
  have hR : 0 ≤ R := (hB 0).1.trans (hB 0).2
  have hS : 0 ≤ S := (hC 0).1.trans (hC 0).2
  apply tendsto_integral_of_dominated_convergence
      (fun p ↦ cosineKernelJet r 0 R (p^2)*cosineKernelJet s 0 S (p^2)*w p)
  · intro k
    exact (newton_pair_integrable (hb k) (hc k) w hw hw0 r s hi).aestronglyMeasurable
  · exact hi
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hnb:=newtonKernel_nonneg (fun i ↦ (hb k i).1) (sq_nonneg p) r
    have hnc:=newtonKernel_nonneg (fun i ↦ (hc k i).1) (sq_nonneg p) s
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hnb hnc) (hw0 p hp))]
    exact mul_le_mul_of_nonneg_right (mul_le_mul
      (newtonKernel_le_jet (fun i ↦ (hb k i).1) (fun i ↦ (hb k i).2) (sq_nonneg p) r)
      (newtonKernel_le_jet (fun i ↦ (hc k i).1) (fun i ↦ (hc k i).2) (sq_nonneg p) s)
      hnc (cosineKernelJet_nonneg hR (sq_nonneg p) r 0)) (hw0 p hp)
  · filter_upwards with p
    apply Tendsto.mul_const
    exact (tendsto_newtonKernel_of_bounded (R:=R+1) (by linarith)
      (fun k i ↦ by rw [abs_of_nonneg (hb k i).1]; linarith [(hb k i).2])
      (fun i ↦ by rw [abs_of_nonneg (hB i).1]; linarith [(hB i).2]) htb (p^2) r).mul
      (tendsto_newtonKernel_of_bounded (R:=S+1) (by linarith)
      (fun k i ↦ by rw [abs_of_nonneg (hc k i).1]; linarith [(hc k i).2])
      (fun i ↦ by rw [abs_of_nonneg (hC i).1]; linarith [(hC i).2]) htc (p^2) s)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory

lemma familyGram_left_combination {n : ℕ} (w : ℝ → ℝ) (F : Fin n → ℝ → ℝ) (G : Fin n → ℝ → ℝ)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (U : Matrix (Fin n) (Fin n) ℝ) :
    familyGram w (fun i ↦ finiteFamilyCombination F (U i)) G=U*familyGram w F G := by
  ext i j
  have he (p : ℝ) : finiteFamilyCombination F (U i) (p^2)*G j (p^2)*w p=
      ∑ l,U i l*(F l (p^2)*G j (p^2)*w p) := by
    simp only [finiteFamilyCombination,sum_mul]
    apply sum_congr rfl
    intro l _
    ring
  simp only [familyGram,he]
  rw [integral_finsetSum _ (fun l _ ↦ (hi l j).const_mul (U i l))]
  simp_rw [integral_const_mul]
  rfl

lemma familyGram_right_combination {n : ℕ} (w : ℝ → ℝ) (F : Fin n → ℝ → ℝ) (G : Fin n → ℝ → ℝ)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (V : Matrix (Fin n) (Fin n) ℝ) :
    familyGram w F (fun i ↦ finiteFamilyCombination G (V i))=familyGram w F G*Vᵀ := by
  ext i j
  have he (p : ℝ) : F i (p^2)*finiteFamilyCombination G (V j) (p^2)*w p=
      ∑ l,V j l*(F i (p^2)*G l (p^2)*w p) := by
    simp only [finiteFamilyCombination,mul_sum,sum_mul]
    apply sum_congr rfl
    intro l _
    ring
  simp only [familyGram,he]
  rw [integral_finsetSum _ (fun l _ ↦ (hi i l).const_mul (V j l))]
  simp_rw [integral_const_mul]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,familyGram,mul_comm]

lemma combination_pair_integrable_left {n : ℕ} (w : ℝ → ℝ) (F : Fin n → ℝ → ℝ) (G : Fin n → ℝ → ℝ)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (U : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (j : Fin n) :
    IntegrableOn (fun p ↦ finiteFamilyCombination F (U i) (p^2)*G j (p^2)*w p) (Set.Ioi 0) := by
  apply (integrable_finsetSum univ (fun l _ ↦ (hi l j).const_mul (U i l))).congr
  filter_upwards with p
  simp only [finiteFamilyCombination,sum_mul]
  apply sum_congr rfl
  intro l _
  ring

lemma familyGram_bichange {n : ℕ} (w : ℝ → ℝ) (F : Fin n → ℝ → ℝ) (G : Fin n → ℝ → ℝ)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (U : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) :
    familyGram w (fun i ↦ finiteFamilyCombination F (U i)) (fun i ↦ finiteFamilyCombination G (V i))=
      U*familyGram w F G*Vᵀ := by
  rw [familyGram_right_combination _ _ _ (combination_pair_integrable_left w F G hi U),
    familyGram_left_combination w F G hi]

lemma residualFamily_combination {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ) (a : ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) :
    residualFamily (fun i ↦ finiteFamilyCombination F (U i)) H a=
      fun i ↦ finiteFamilyCombination (residualFamily F H a) (U i) := by
  funext i x
  simp only [residualFamily,finiteFamilyCombination,sum_mul,sum_div,←sum_sub_distrib,mul_sub]
  apply sum_congr rfl
  intro l _
  ring

lemma meanResidualRatio_bichange {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a : ℝ)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p ↦ H (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (U V : Matrix (Fin n) (Fin n) ℝ) (hU : U.det≠0) (hV : V.det≠0) :
    meanResidualRatio w (fun i ↦ finiteFamilyCombination F (U i))
      (fun i ↦ finiteFamilyCombination G (V i)) H a=meanResidualRatio w F G H a := by
  unfold meanResidualRatio
  rw [residualFamily_combination,familyGram_bichange _ _ _ (residualFamily_pair_integrable w F G H a hi hH),
    familyGram_bichange _ _ _ hi]
  simp only [Matrix.det_mul,Matrix.det_transpose]
  rw [mul_div_mul_right _ _ hV,mul_div_mul_left _ _ hU]

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Matrix Filter Topology MeasureTheory

lemma jet_meanResidualRatio_eq_newton {n : ℕ} (b c : ℕ → ℝ) {R S : ℝ}
    (hb : ∀ i,0 ≤ b i ∧ b i≤R) (hc : ∀ i,0 ≤ c i ∧ c i≤S)
    (w : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀ p,0<p → 0≤w p)
    (H : ℝ → ℝ) (a : ℝ)
    (hi : ∀ r s,IntegrableOn (fun p ↦ cosineKernelJet r 0 R (p^2)*cosineKernelJet s 0 S (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ j : Fin n,IntegrableOn (fun p ↦ H (p^2)*newtonKernel c (p^2) 0 j*w p) (Set.Ioi 0)) :
    meanResidualRatio w (fun i : Fin n ↦ cosineKernelJet (nodalOrder b i) 0 (b i))
      (fun i : Fin n ↦ cosineKernelJet (nodalOrder c i) 0 (c i)) H a=
    meanResidualRatio w (fun i : Fin n ↦ fun x ↦ newtonKernel b x 0 i)
      (fun i : Fin n ↦ fun x ↦ newtonKernel c x 0 i) H a := by
  have hR : 0≤R := (hb 0).1.trans (hb 0).2
  have hS : 0≤S := (hc 0).1.trans (hc 0).2
  have he (d : ℕ → ℝ) (T : ℝ) (hT : 0≤T) (hd : ∀ i,0 ≤ d i ∧ d i≤T) :
      (fun i : Fin n ↦ cosineKernelJet (nodalOrder d i) 0 (d i))=
      (fun i ↦ finiteFamilyCombination (fun j : Fin n ↦ fun x ↦ newtonKernel d x 0 j) ((newtonJetMatrix n d)ᵀ i)) := by
    funext i x
    simpa only [finiteFamilyCombination,Matrix.transpose_apply,mul_comm] using cosineKernelJet_newton (R:=T+1) (by linarith)
      (fun j ↦ by rw [abs_of_nonneg (hd j).1]; linarith [(hd j).2]) x 0 i
  rw [he b R hR hb,he c S hS hc]
  exact meanResidualRatio_bichange w _ _ H a
    (fun i j ↦ newton_pair_integrable hb hc w hw hw0 i j (hi i j)) hH _ _
    (by rw [Matrix.det_transpose]; exact newtonJetMatrix_det_ne_zero n b)
    (by rw [Matrix.det_transpose]; exact newtonJetMatrix_det_ne_zero n c)

lemma tendsto_newton_meanResidualRatio {n : ℕ} {b c : ℕ → ℕ → ℝ} {B C : ℕ → ℝ} {R S T : ℝ}
    (hb : ∀ k i,0 ≤ b k i ∧ b k i≤R) (hc : ∀ k i,0 ≤ c k i ∧ c k i≤S)
    (hB : ∀ i,0 ≤ B i ∧ B i≤R) (hC : ∀ i,0 ≤ C i ∧ C i≤S)
    (htb : Tendsto b atTop (𝓝 B)) (htc : Tendsto c atTop (𝓝 C))
    (w : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀ p,0<p → 0≤w p) (hT : 0≤T)
    (hi : ∀ r s,IntegrableOn (fun p ↦ cosineKernelJet r 0 R (p^2)*cosineKernelJet s 0 S (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ s,IntegrableOn (fun p ↦ cosineKernelJet 0 0 T (p^2)*cosineKernelJet s 0 S (p^2)*w p) (Set.Ioi 0))
    (hd : (familyGram w (fun i : Fin n ↦ fun x ↦ newtonKernel B x 0 i)
      (fun i : Fin n ↦ fun x ↦ newtonKernel C x 0 i)).det≠0) :
    Tendsto (fun k ↦ meanResidualRatio w (fun i : Fin n ↦ fun x ↦ newtonKernel (b k) x 0 i)
      (fun i : Fin n ↦ fun x ↦ newtonKernel (c k) x 0 i) (cosineKernelJet 0 0 T) 0)
      atTop (𝓝 (meanResidualRatio w (fun i : Fin n ↦ fun x ↦ newtonKernel B x 0 i)
        (fun i : Fin n ↦ fun x ↦ newtonKernel C x 0 i) (cosineKernelJet 0 0 T) 0)) := by
  let F k := fun i : Fin n ↦ fun x ↦ newtonKernel (b k) x 0 i
  let G k := fun i : Fin n ↦ fun x ↦ newtonKernel (c k) x 0 i
  let f := fun i : Fin n ↦ fun x ↦ newtonKernel B x 0 i
  let g := fun i : Fin n ↦ fun x ↦ newtonKernel C x 0 i
  let H := cosineKernelJet 0 0 T
  have hR : 0≤R := (hB 0).1.trans (hB 0).2
  have hM : Tendsto (fun k ↦ familyGram w (F k) (G k)) atTop (𝓝 (familyGram w f g)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact tendsto_newton_pair_integral hb hc hB hC htb htc w hw hw0 i j (hi i j)
  have hMom : Tendsto (fun k ↦ fun j : Fin n ↦ ∫ p in Set.Ioi 0,H (p^2)*G k j (p^2)*w p)
      atTop (𝓝 (fun j : Fin n ↦ ∫ p in Set.Ioi 0,H (p^2)*g j (p^2)*w p)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [newtonKernel_const,H,G,g] using tendsto_newton_pair_integral
      (fun _ _ ↦ ⟨hT,le_rfl⟩) hc (fun _ ↦ ⟨hT,le_rfl⟩) hC tendsto_const_nhds htc
      w hw hw0 0 j (hH j)
  have hFi : ∀ i : Fin n,Tendsto (fun k ↦ F k i 0) atTop (𝓝 (f i 0)) := by
    intro i
    exact tendsto_newtonKernel_of_bounded (R:=R+1) (by linarith)
      (fun k j ↦ by rw [abs_of_nonneg (hb k j).1]; linarith [(hb k j).2])
      (fun j ↦ by rw [abs_of_nonneg (hB j).1]; linarith [(hB j).2]) htb 0 i
  have hi₁ k (i j : Fin n) := newton_pair_integrable (hb k) (hc k) w hw hw0 i j (hi i j)
  have hi₂ (i j : Fin n) := newton_pair_integrable hB hC w hw hw0 i j (hi i j)
  have hh₁ k (j : Fin n) : IntegrableOn (fun p ↦ H (p^2)*G k j (p^2)*w p) (Set.Ioi 0) := by
    simpa only [newtonKernel_const,H,G] using newton_pair_integrable (fun _ ↦ ⟨hT,le_rfl⟩) (hc k) w hw hw0 0 j (hH j)
  have hh₂ (j : Fin n) : IntegrableOn (fun p ↦ H (p^2)*g j (p^2)*w p) (Set.Ioi 0) := by
    simpa only [newtonKernel_const,H,g] using newton_pair_integrable (fun _ ↦ ⟨hT,le_rfl⟩) hC w hw hw0 0 j (hH j)
  have hRes : Tendsto (fun k ↦ familyGram w (residualFamily (F k) H 0) (G k)) atTop
      (𝓝 (familyGram w (residualFamily f H 0) g)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simp only [residualFamily_gram w (F _) (G _) H 0 (hi₁ _) (hh₁ _),
      residualFamily_gram w f g H 0 hi₂ hh₂,Matrix.sub_apply,Matrix.vecMulVec_apply]
    exact ((hM.apply_nhds i).apply_nhds j).sub
      (((hFi i).div_const (H 0)).mul (hMom.apply_nhds j))
  exact ((continuous_id.matrix_det.tendsto _).comp hRes).div
    ((continuous_id.matrix_det.tendsto _).comp hM) hd

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Filter Topology

noncomputable def commonApproach (N : ℕ) (ε : ℝ) (k : ℕ) : ℝ :=
  if k < N then ε*((k:ℝ)+1)/((N:ℝ)+1) else angle^2-ε*((2*N-k:ℕ):ℝ)/((N:ℝ)+1)
noncomputable def interiorApproach (N : ℕ) (τ ε : ℝ) (k : ℕ) : ℝ :=
  if k < N then commonApproach N ε k else if k=N then τ else commonApproach N ε (k-1)

lemma commonApproach_low {N k : ℕ} (hk : k < N) {ε : ℝ} (he : 0 ≤ ε) :
    0 ≤ commonApproach N ε k ∧ commonApproach N ε k ≤ ε := by
  rw [commonApproach,ite_eq_left hk]
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < (N:ℝ)+1)).mpr
    have h : (k:ℝ)+1 ≤ (N:ℝ)+1 := by exact_mod_cast (show k+1 ≤ N+1 by omega)
    exact mul_le_mul_of_nonneg_left h he

lemma commonApproach_high {N k : ℕ} (hk : N ≤ k) {ε : ℝ} (he : 0 ≤ ε) :
    angle^2-ε ≤ commonApproach N ε k ∧ commonApproach N ε k ≤ angle^2 := by
  rw [commonApproach,ite_eq_right (by omega)]
  have hlo : 0 ≤ ε*((2*N-k:ℕ):ℝ)/((N:ℝ)+1) := by positivity
  have hhi : ε*((2*N-k:ℕ):ℝ)/((N:ℝ)+1) ≤ ε := by
    apply (div_le_iff₀ (by positivity : 0 < (N:ℝ)+1)).mpr
    apply mul_le_mul_of_nonneg_left _ he
    exact_mod_cast (show 2*N-k ≤ N+1 by omega)
  constructor  <;> linarith

lemma commonApproach_bounds (N k : ℕ) {ε : ℝ} (he : 0 ≤ ε) (heL : ε ≤ angle^2) :
    0 ≤ commonApproach N ε k ∧ commonApproach N ε k ≤ angle^2 := by
  by_cases hk : k < N
  · exact ⟨(commonApproach_low hk he).1,(commonApproach_low hk he).2.trans heL⟩
  · have h:=commonApproach_high (by omega : N ≤ k) he
    constructor  <;> linarith [h.1,h.2]

lemma commonApproach_strictMono (N : ℕ) {ε : ℝ} (he : 0 < ε) (heL : 2*ε < angle^2) :
    StrictMono (fun i : Fin (2*N) ↦ commonApproach N ε i) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  by_cases hj : j.val < N
  · have hi : i.val < N := lt_trans hij' hj
    simp only [commonApproach,hi,hj,ite_true]
    apply (div_lt_div_iff_of_pos_right (by positivity : 0 < (N:ℝ)+1)).mpr
    apply mul_lt_mul_of_pos_left _ he
    exact_mod_cast (show i.val+1 < j.val+1 by omega)
  · by_cases hi : i.val < N
    · exact lt_of_le_of_lt (commonApproach_low hi he.le).2
        (lt_of_lt_of_le (by linarith) (commonApproach_high (by omega : N ≤ j.val) he.le).1)
    · simp only [commonApproach,hi,hj,ite_false]
      apply sub_lt_sub_left
      apply (div_lt_div_iff_of_pos_right (by positivity : 0 < (N:ℝ)+1)).mpr
      apply mul_lt_mul_of_pos_left _ he
      exact_mod_cast (show 2*N-j.val < 2*N-i.val by have := j.isLt; omega)

lemma interiorApproach_bounds (N k : ℕ) {τ ε : ℝ} (he : 0 ≤ ε) (heL : ε ≤ angle^2)
    (ht : 0 ≤ τ ∧ τ ≤ angle^2) :
    0 ≤ interiorApproach N τ ε k ∧ interiorApproach N τ ε k ≤ angle^2 := by
  unfold interiorApproach
  split_ifs  <;> first | exact ht | exact commonApproach_bounds N _ he heL

lemma interiorApproach_strictMono (N : ℕ) {τ ε : ℝ} (he : 0 < ε)
    (hl : ε < τ) (hr : τ < angle^2-ε) :
    StrictMono (fun i : Fin (2*N+1) ↦ interiorApproach N τ ε i) := by
  have heL : 2*ε < angle^2 := by linarith
  have hq:=commonApproach_strictMono N he heL
  intro i j hij
  have hiN := i.isLt
  have hjN := j.isLt
  have hij' : i.val < j.val := hij
  by_cases hj : j.val < N
  · have hi : i.val < N := lt_trans hij' hj
    simp only [interiorApproach,hi,hj,ite_true]
    exact hq (show (⟨i.val,by omega⟩ : Fin (2*N)) < ⟨j.val,by omega⟩ from hij')
  · by_cases hi : i.val < N
    · simp only [interiorApproach,hi,hj,ite_true,ite_false]
      split_ifs with hje
      · exact (commonApproach_low hi he.le).2.trans_lt hl
      · exact (commonApproach_low hi he.le).2.trans_lt
          (lt_of_lt_of_le (by linarith) (commonApproach_high (by omega : N ≤ j.val-1) he.le).1)
    · simp only [interiorApproach,hi,hj,ite_false]
      have hje : j.val≠N := by omega
      rw [ite_eq_right hje]
      split_ifs with hie
      · exact hr.trans_le (commonApproach_high (by omega : N ≤ j.val-1) he.le).1
      · exact hq (show (⟨i.val-1,by omega⟩ : Fin (2*N)) < ⟨j.val-1,by omega⟩ by change i.val-1 < j.val-1; omega)

lemma nodalOrder_eq_zero_of_strictMono_prefix {b : ℕ → ℝ} {n : ℕ}
    (hb : StrictMono (fun i : Fin n ↦ b i)) (i : Fin n) : nodalOrder b i=0 := by
  unfold nodalOrder
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro j hj
  have hj' : j < i.val := Finset.mem_range.mp hj
  exact (hb (show (⟨j,by omega⟩ : Fin n) < i from hj')).ne

lemma interiorApproach_permutation (N : ℕ) (τ ε : ℝ) (i : Fin (2*N+1)) :
    interiorApproach N τ ε (knotPermutation N i)=Fin.lastCases τ (fun j : Fin (2*N) ↦ commonApproach N ε j) i := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [knotPermutation_last]
    simp [interiorApproach]
  · rw [knotPermutation_castSucc]
    by_cases hj : j.val < N
    · simp [interiorApproach,insertKnotIndex,hj]
    · have hl : ¬j.val+1 < N := by omega
      have hn : j.val+1≠N := by omega
      simp [interiorApproach,insertKnotIndex,hj,hl,hn]

lemma tendsto_commonApproach (N : ℕ) {ε : ℕ → ℝ} (he : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k ↦ commonApproach N (ε k)) atTop (𝓝 (twoKnotLabels N)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  by_cases hi : i < N
  · simpa only [commonApproach,twoKnotLabels,hi,ite_true,zero_mul,zero_div] using
      (he.mul_const ((i:ℝ)+1)).div_const ((N:ℝ)+1)
  · simpa only [commonApproach,twoKnotLabels,hi,ite_false,zero_mul,zero_div,sub_zero] using
      tendsto_const_nhds.sub ((he.mul_const ((2*N-i:ℕ):ℝ)).div_const ((N:ℝ)+1))

lemma tendsto_interiorApproach (N : ℕ) (t : ℝ) {ε : ℕ → ℝ} (he : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k ↦ interiorApproach N (t^2) (ε k)) atTop (𝓝 (interiorKnotLabels N t)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hq:=tendsto_commonApproach N he
  by_cases hi : i < N
  · simpa [interiorApproach,interiorKnotLabels,twoKnotLabels,hi] using hq.apply_nhds i
  · by_cases hie : i=N
    · simp [interiorApproach,interiorKnotLabels,hie]
    · have hi' : ¬i-1 < N := by omega
      simpa [interiorApproach,interiorKnotLabels,twoKnotLabels,hi,hie,hi'] using hq.apply_nhds (i-1)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
