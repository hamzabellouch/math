import OAI.Geometry.UnitDistances.PredictionBudget

namespace OAI

namespace PlanarUnitDistances.IncidenceNoise
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params)
def dp (i : ℕ) : ℝ := s.t i^(-1/2:ℝ)
def collision (i : ℕ) : ℝ := (capacity a:ℝ)^(length s a i)*dp s i
def rootInfo (i : ℕ) : ℝ := (IncidenceSequence.information (s.P i) (s.Q i)/(length s a i:ℝ))^(1/4:ℝ)
def noise (i : ℕ) : ℝ := |(2*Real.log 2+4)/scale s i|+collision s a i+vanishing i+rootInfo s a i
lemma tpos (i : ℕ) : 0 < s.t i := by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i]
lemma dp_nonneg (i : ℕ) : 0 ≤ dp s i := Real.rpow_nonneg (tpos s i).le _
lemma collision_nonneg (i : ℕ) : 0 ≤ collision s a i := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (dp_nonneg s i)
lemma root_nonneg (i : ℕ) : 0 ≤ rootInfo s a i := Real.rpow_nonneg
  (div_nonneg (s.good i).information_nonneg (Nat.cast_nonneg _)) _
lemma nonneg (i : ℕ) : 0 ≤ noise s a i := by
  unfold noise
  have h₁ := collision_nonneg s a i
  have h₂ := root_nonneg s a i
  have h₃ := vanishing_pos i
  positivity
lemma limit : Tendsto (noise s a) atTop (nhds 0) := by
  have h₀ : Tendsto (fun i => |(2*Real.log 2+4)/scale s i|) atTop (nhds 0) := by
    simpa only [abs_zero] using (tendsto_const_nhds.div_atTop (scale_limit s)).abs
  have h₁ : Tendsto (collision s a) atTop (nhds 0) :=
    LogHistory.density_limit (capacity_pos a) s.t (dp s) s.tendsto
      (Eventually.of_forall (dp_nonneg s)) (Eventually.of_forall (fun _ => le_rfl))
  have hi := LogHistory.ratio_limit (capacity_pos a) s.t
    (fun i => IncidenceSequence.information (s.P i) (s.Q i)) s.tendsto
    (Eventually.of_forall (fun i => (s.good i).information_nonneg)) s.information_limit
  have h₂ : Tendsto (rootInfo s a) atTop (nhds 0) := by
    exact hi.rpow_const_nhds_zero (by norm_num)
  change Tendsto (fun i => |(2*Real.log 2+4)/scale s i|+collision s a i+vanishing i+rootInfo s a i) atTop (nhds 0)
  convert ((h₀.add h₁).add vanishing_limit).add h₂ using 1; norm_num
lemma components (i : ℕ) :
    |(2*Real.log 2+4)/scale s i| ≤ noise s a i ∧ collision s a i ≤ noise s a i ∧
      vanishing i ≤ noise s a i ∧ rootInfo s a i ≤ noise s a i := by
  have h₀ := abs_nonneg ((2*Real.log 2+4)/scale s i)
  have h₁ := collision_nonneg s a i
  have h₂ := (vanishing_pos i).le
  have h₃ := root_nonneg s a i
  unfold noise
  constructor; linarith
  constructor; linarith
  constructor <;> linarith
lemma dp_le_collision (i : ℕ) : dp s i ≤ collision s a i := by
  have hc : (1:ℝ) ≤ capacity a := by exact_mod_cast capacity_pos a
  have hh := one_le_pow₀ (n:=length s a i) hc
  exact (one_mul (dp s i)).symm.le.trans (mul_le_mul_of_nonneg_right hh (dp_nonneg s i))
lemma row_atom (i : ℕ) (p : s.P i) (q : s.Q i) :
    (FiniteStarCoupling.row (graph s i) p).val q ≤ dp s i := by
  have hr := row_bound s i p q
  rw [one_div,←Real.rpow_neg (tpos s i).le] at hr
  simpa only [dp,neg_div] using hr
lemma row (i : ℕ) (p : s.P i) (q : s.Q i) :
    (graph s i).val (p,q) ≤ dp s i*(left (graph s i)).val p := by
  rw [←row_weight]
  have hr := row_bound s i p q
  rw [one_div,←Real.rpow_neg (tpos s i).le] at hr
  have hh := mul_le_mul_of_nonneg_left hr ((left (graph s i)).nonneg p)
  simpa only [dp,neg_div,mul_comm] using hh
lemma column (i : ℕ) (p : s.P i) (q : s.Q i) :
    (graph s i).val (p,q) ≤ vanishing i*(right (graph s i)).val q := by
  have hp := (s.good i).center_degree_pos q
  have he := (s.good i).positive
  have hb := (le_div_iff₀ he).mp ((s.good i).atomQ q q.property)
  have hd : (i:ℝ)+1 ≤ CircleIncidence.degree (s.P i) q :=
    (s.good i).degreeQ.trans (by simpa only [div_mul_eq_mul_div] using hb)
  have hv : (col (graph s i) q).val p ≤ vanishing i := by
    rw [graph,GeometricLaw.graph,UniformGraphLaw.col_eq _ _ (by rw [GeometricLaw.degree_eq]; exact hp),GeometricLaw.degree_eq]
    apply le_trans (div_le_div_of_nonneg_right (b:=(1:ℝ)) ?_ hp.le)
    · exact one_div_le_one_div_of_le (by positivity) hd
    · unfold IncidenceEntropy.indicator
      split_ifs <;> norm_num
  rw [←col_weight]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hv ((right (graph s i)).nonneg q)
end
end PlanarUnitDistances.IncidenceNoise

namespace PlanarUnitDistances.IncidenceEstimates
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}
local instance : Fintype (s.P i⊕s.Q i) := inferInstance
local instance : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := snapshotFintype _ _ _
variable (R : Realization s a i)

lemma template_collision : (Fintype.card (Fin a.k → FiniteInformation.History
      (Fin a.m×Fin a.m) R.depth):ℝ)*dp s i ≤ collision s a i := by
  have hh : Fintype.card (Fin a.k → FiniteInformation.History (Fin a.m×Fin a.m) R.depth) ≤
      capacity a^(length s a i) := by
    simp only [Fintype.card_fun,FiniteInformation.history_card,Fintype.card_prod,Fintype.card_fin]
    rw [←pow_two,←pow_mul,←pow_mul]
    unfold capacity
    rw [←pow_mul]
    apply Nat.pow_le_pow_right a.m_pos
    nlinarith [R.depth_lt]
  unfold collision
  apply mul_le_mul_of_nonneg_right _ (dp_nonneg s i)
  exact_mod_cast hh
lemma history_collision : (Fintype.card (FiniteInformation.History
      (Fin a.m×Fin a.m) R.depth):ℝ)*dp s i ≤ collision s a i := by
  have hc : Fintype.card (FiniteInformation.History (Fin a.m×Fin a.m) R.depth) ≤
      Fintype.card (Fin a.k → FiniteInformation.History (Fin a.m×Fin a.m) R.depth) := by
    apply Fintype.card_le_of_injective (fun x (_ : Fin a.k) => x)
    intro x y h
    exact congrFun h ⟨0,a.k_pos⟩
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (dp_nonneg s i)).trans (template_collision R)

theorem basic {C L : ℝ} (hC : 0<C) (hv : R.Valid C L) (hscale : 0<scale s i) :
    let B := R.book
    let r := noise s a i
    B.M ≤ r*B.S ∧ B.WC ≤ (1/a.epsilon)*B.S ∧ B.WB ≤ (r/a.epsilon)*B.S ∧
    B.HP+B.HQ ≤ BookEnvelope.height C r*B.S ∧
    B.J ≤ BookEnvelope.j a C (27/50) (1/25) (s.ξ i) r*B.S ∧
    B.EP ≤ BookEnvelope.pred a r*B.S := by
  let B := R.book
  let r := noise s a i
  obtain ⟨hf,hS,hM,hcard,hst,hrare,hWC,hWB,hH,hJ,hW,hEP⟩ := hv
  obtain ⟨hSn,hMn,hPn,hQn,hCPn,hCQn,hJn,hWCn,hWBn⟩ := B.nonneg
  have he := a.epsilon_pos
  have hr := nonneg s a i
  have hn := components s a i
  have hd := (dp_le_collision s a i).trans hn.2.1
  have hc : 2*Real.log 2+4 ≤ r*scale s i :=
    (div_le_iff₀ hscale).mp ((le_abs_self _).trans hn.1)
  have hM' : B.M ≤ r*B.S := by
    as_aux_lemma =>
      apply (mul_le_mul_iff_right₀ R.mass_pos).mp
      calc
        mass (model s i).support*B.M ≤ 2*Real.log 2+4 := hM
        _ ≤ r*scale s i := hc
        _ = mass (model s i).support*(r*B.S) := by rw [←hS]; ring
  have hWC' : B.WC ≤ (1/a.epsilon)*B.S := by simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using (show B.WC≤B.S/a.epsilon from hWC)
  have hWB' : B.WB ≤ (r/a.epsilon)*B.S := by
    as_aux_lemma =>
      calc
        _ ≤ B.M/a.epsilon := hWB
        _ ≤ (r*B.S)/a.epsilon := div_le_div_of_nonneg_right hM' a.epsilon_pos.le
        _ = _ := by ring
  have hH' : B.HP+B.HQ ≤ BookEnvelope.height C r*B.S := by
    as_aux_lemma =>
      calc
        _ ≤ C*(B.S+B.M) := hH
        _ ≤ C*(B.S+r*B.S) := by gcongr
        _ = _ := by unfold BookEnvelope.height; ring
  have hj0 : 0 ≤ BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i) := by
    unfold BudgetParameters.joint
    have hx := (s.good i).error_nonneg
    positivity
  have hJ' : B.J ≤ BookEnvelope.j a C (27/50) (1/25) (s.ξ i) r*B.S := by
    as_aux_lemma =>
      calc
        _ ≤ BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i)/2*(B.HP+B.HQ) := hJ
        _ ≤ BudgetParameters.joint C (27/50) (1/25) a.epsilon (s.ξ i)/2*(BookEnvelope.height C r*B.S) := by gcongr
        _ = _ := by unfold BookEnvelope.j; ring
  have hEP' : B.EP ≤ BookEnvelope.pred a r*B.S := by
    as_aux_lemma =>
      calc
        _ ≤ B.M+B.WC*(4/(a.m:ℝ)+18*rootInfo s a i) := hEP
        _ ≤ r*B.S+((1/a.epsilon)*B.S)*(4/(a.m:ℝ)+18*r) := by
          gcongr
          · have hroot := root_nonneg s a i; positivity
          · exact hn.2.2.2
        _ = _ := by unfold BookEnvelope.pred; ring
  exact ⟨hM',hWC',hWB',hH',hJ',hEP'⟩

lemma raw_point : R.book.DP ≤ R.book.CP/20000000+2*Real.log 2/mass (model s i).support+2*dp s i*(R.book.WC+R.book.HP) := by
  have hu := fun p q h => (model s i).unit_identity p q (support s i p q h)
  have h := ActualBookUpper.point (model s i).support (model s i).z (model s i).w Sum.inl Sum.inr R.shifts
    (graph s i) R.history a.epsilon_pos a.epsilon_lt R.good R.label R.mass_pos
    hu (model s i).center_injective (model s i).sub_mem (model s i).difference_mem (IncidenceNoise.row s i)
  exact h

lemma raw_center : R.book.DQ ≤ R.book.CQ/20000000+2*Real.log 2/mass (model s i).support+2*vanishing i*(R.book.WC+R.book.HQ) := by
  have hu := fun p q h => (model s i).unit_identity p q (support s i p q h)
  have h := ActualBookUpper.center (model s i).support (model s i).z (model s i).w Sum.inl Sum.inr R.shifts
    (graph s i) R.history a.epsilon_pos a.epsilon_lt R.good R.label R.mass_pos
    hu (model s i).point_injective (model s i).sub_mem (model s i).difference_mem (IncidenceNoise.column s i)
  exact h

lemma raw_template : Book.DT (I:=Fin a.k) R.book ≤ Book.CT (I:=Fin a.k) R.book/20000000+2*Real.log 2/mass (model s i).support+
    2*(Fintype.card (Fin a.k → FiniteInformation.History (Fin a.m×Fin a.m) R.depth):ℝ)*dp s i*(R.book.WC+R.book.HP) := by
  have hu := fun p q h => (model s i).unit_identity p q (support s i p q h)
  have h := ActualBookUpper.template (I:=Fin a.k) (model s i).support (model s i).z (model s i).w Sum.inl Sum.inr R.shifts
    (graph s i) R.history a.epsilon_pos a.epsilon_lt R.good R.label R.mass_pos
    hu (model s i).center_injective (model s i).sub_mem (model s i).difference_mem (IncidenceNoise.row s i)
  simpa only [Fintype.card_fun,Realization.book,Realization.input,ActualProfiles.Input.book] using h

lemma raw_prediction : R.book.T ≤ 2*R.book.HP+2*Real.log 2/mass (model s i).support+R.book.WB+
    R.book.WC*((Fintype.card (FiniteInformation.History (Fin a.m×Fin a.m) R.depth):ℝ)*dp s i) := by
  have h := ActualBookUpper.prediction (model s i).support (model s i).z (model s i).w Sum.inl Sum.inr R.shifts
    (graph s i) R.history a.epsilon R.good R.label R.mass_pos (model s i).point_injective (model s i).wpoint_injective
    (model s i).sub_mem (model s i).wsub_mem (dp_nonneg s i) (point_bound s i)
  exact h

lemma star_upper {D A c d W H r S u v : ℝ}
    (hraw : D≤A/20000000+c+2*d*(W+H)) (hc : c≤r*S) (hd : d≤r) (hr : 0≤r)
    (hW0 : 0≤W) (hH0 : 0≤H) (hW : W≤u*S) (hH : H≤v*S) :
    D≤A/20000000+(r+2*r*(u+v))*S := by
  calc
    _ ≤ _ := hraw
    _ ≤ A/20000000+r*S+2*r*(u*S+v*S) := by gcongr
    _ = _ := by ring
lemma prediction_upper {D H c WB WC d r S ε : ℝ}
    (hraw : D≤2*H+c+WB+WC*d) (hc : c≤r*S) (hB : WB≤(r/ε)*S)
    (hW : WC≤(1/ε)*S) (hW0 : 0≤WC) (hd : d≤r) (hr : 0≤r) :
    D≤2*H+(r+r/ε+r/ε)*S := by
  calc
    _ ≤ _ := hraw
    _ ≤ 2*H+r*S+(r/ε)*S+WC*r := by gcongr
    _ ≤ 2*H+r*S+(r/ε)*S+((1/ε)*S)*r := by gcongr
    _ = _ := by ring

theorem upper {C L : ℝ} (hC : 0<C) (hv : R.Valid C L) (hscale : 0<scale s i) :
    let B := R.book
    let r := noise s a i
    B.M ≤ r*B.S ∧ B.WC ≤ (1/a.epsilon)*B.S ∧ B.WB ≤ (r/a.epsilon)*B.S ∧
    B.HP+B.HQ ≤ BookEnvelope.height C r*B.S ∧
    B.J ≤ BookEnvelope.j a C (27/50) (1/25) (s.ξ i) r*B.S ∧
    B.EP ≤ BookEnvelope.pred a r*B.S ∧
    B.DP ≤ B.CP/20000000+BookEnvelope.star a C r*B.S ∧
    B.DQ ≤ B.CQ/20000000+BookEnvelope.star a C r*B.S ∧
    Book.DT (I:=Fin a.k) B ≤ Book.CT (I:=Fin a.k) B/20000000+BookEnvelope.star a C r*B.S ∧
    B.T ≤ 2*B.HP+BookEnvelope.prediction a r*B.S := by
  let B := R.book
  let r := noise s a i
  have hbasic := basic R hC hv hscale
  obtain ⟨hf,hS,hM,hcard,hst,hrare,hWC,hWB,hH,hJ,hW,hEP⟩ := hv
  obtain ⟨hSn,hMn,hPn,hQn,hCPn,hCQn,hJn,hWCn,hWBn⟩ := B.nonneg
  have he := a.epsilon_pos
  have hr := nonneg s a i
  have hn := components s a i
  have hd := (dp_le_collision s a i).trans hn.2.1
  have hc : 2*Real.log 2+4 ≤ r*scale s i :=
    (div_le_iff₀ hscale).mp ((le_abs_self _).trans hn.1)
  obtain ⟨hM',hWC',hWB',hH',hJ',hEP'⟩ := hbasic
  have hconst : 2*Real.log 2/mass (model s i).support ≤ r*B.S := by
    as_aux_lemma =>
      apply (div_le_iff₀ R.mass_pos).mpr
      rw [←hS] at hc
      nlinarith
  have hP : B.HP ≤ BookEnvelope.height C r*B.S := by linarith
  have hQ : B.HQ ≤ BookEnvelope.height C r*B.S := by linarith
  have hp := star_upper (raw_point R) hconst hd hr hWCn hPn hWC' hP
  have hq := star_upper (raw_center R) hconst hn.2.2.1 hr hWCn hQn hWC' hQ
  have ht0 := raw_template R
  rw [mul_assoc 2 _ (dp s i)] at ht0
  have ht := star_upper ht0 hconst ((template_collision R).trans hn.2.1) hr hWCn hPn hWC' hP
  have hpr := prediction_upper (raw_prediction R) hconst hWB' hWC' hWCn
    ((history_collision R).trans hn.2.1) hr
  exact ⟨hM',hWC',hWB',hH',hJ',hEP',hp,hq,ht,hpr⟩
end
end PlanarUnitDistances.IncidenceEstimates

namespace PlanarUnitDistances.EnvelopeCoercivity
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook BudgetParameters
  BookEnvelope BookCoercivity
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A]
variable (B : Book D P Q H A) (a : Params) {C L ξ r : ℝ}

def pointConstant (L : ℝ) : ℝ := 400000*L+2
def lossConstant (L : ℝ) : ℝ := 23000000000*L+130001

theorem bounds (hC : 0<C) (hL : 0≤L) (hξ : 0≤ξ) (hr : 0≤r)
    (hμ : ∀p,0<(left B.graph).val p) (hκ : ∀q,0<(right B.graph).val q)
    (hst : ∀d,minorityMass B.graph (B.bit d) ≤ L*(VP B.graph (B.bit d)+VQ B.graph (B.bit d)))
    (hra : ∀d,B.R d → minorityMass B.graph (B.bit d) ≤ hp B.graph (B.bit d) (B.point d) (B.label d)+
      hq B.graph (B.bit d) (B.center d) (B.label d)+RareLabels.error B.graph (B.bit d) (B.point d) (B.center d))
    (hM : B.M ≤ r*B.S) (hWC : B.WC ≤ (1/a.epsilon)*B.S) (hWB : B.WB ≤ (r/a.epsilon)*B.S)
    (hJ : B.J ≤ j a C (27/50) (1/25) ξ r*B.S) (hEP : B.EP ≤ pred a r*B.S)
    (hDP : B.DP ≤ B.CP/20000000+star a C r*B.S)
    (hDQ : B.DQ ≤ B.CQ/20000000+star a C r*B.S)
    (hDT : Book.DT (I:=Fin a.k) B ≤ Book.CT (I:=Fin a.k) B/20000000+star a C r*B.S)
    (hT : B.T ≤ 2*B.HP+prediction a r*B.S) :
    B.CQ ≤ 250000*total a C (27/50) (1/25) ξ r*B.S ∧
    B.HQ ≤ B.HP+130000*total a C (27/50) (1/25) ξ r*B.S ∧
    B.S ≤ pointConstant L*B.HP+lossConstant L*total a C (27/50) (1/25) ξ r*B.S := by
  have hk : (Fintype.card (Fin a.k):ℝ)*a.zeta<1 := by
    rw [Fintype.card_fin,a.k_zeta]; norm_num
  have hh := CoercivityAll.all (I:=Fin a.k) B hμ hκ a.zeta_pos hk
    (by simpa only [Fintype.card_fin] using a.k_pos) a.eta_pos a.eta_lt a.delta_pos hL
    (fun d _ => hst d) (fun d h₁ h₂ => hra d ⟨h₁,h₂⟩) hDP hDQ hDT hT
  have he := BookEnvelope.bounds a C (27/50) (1/25) ξ r B hC.le (by norm_num) hξ hr hM hWC hWB hJ hEP
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ 250000*loss (I:=Fin a.k) B a.zeta a.eta a.delta
          (star a C r*B.S) (star a C r*B.S) (star a C r*B.S) (prediction a r*B.S) := hh.1
      _ ≤ _ := by linarith
  · linarith [mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤130000)]
  · have hc : 0≤lossConstant L := by unfold lossConstant; positivity
    have ht := mul_le_mul_of_nonneg_left he hc
    dsimp only [pointConstant,lossConstant] at ht ⊢
    linarith [hh.2.2]

omit [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A] in
lemma positive_fraction {S HP L E : ℝ} (hL : 0≤L) (hS : 0≤S)
    (h : S≤pointConstant L*HP+lossConstant L*E*S) (hE : lossConstant L*E≤1/2) :
    S/(2*pointConstant L)≤HP := by
  have hp : 0<pointConstant L := by unfold pointConstant; positivity
  have ht := mul_le_mul_of_nonneg_right hE hS
  apply (div_le_iff₀ (by positivity : 0<2*pointConstant L)).mpr
  nlinarith
end
end PlanarUnitDistances.EnvelopeCoercivity

namespace PlanarUnitDistances.ProfileBudget
open MeasureTheory Set Finset FiniteLaw FiniteLawIntegral FiniteStarCoupling LevelSnapshot
  ScoreBook ActualScoreBook PlaceLevels ActualProfiles
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)

def weighted (f : Place K G.support → ℝ) : ℝ := (LevelScale.weight K : ℝ)*∑v,f v
def l1 (f : Place K G.support → ℝ) : ℝ := weighted G (fun v => |f v|)
def height (p : P) : ℝ := weighted G (G.heightAt p)
def error (i : Bool) (a : Q×(P×P)) : ℝ := weighted G (G.errorAt i a)

lemma weighted_nonneg {f : Place K G.support → ℝ} (hf : ∀v,0≤f v) : 0 ≤ weighted G f :=
  mul_nonneg (NNReal.coe_nonneg _) (sum_nonneg fun v _ => hf v)
lemma weighted_mono {f g : Place K G.support → ℝ} (hf : ∀v,f v≤g v) : weighted G f ≤ weighted G g :=
  mul_le_mul_of_nonneg_left (sum_le_sum fun v _ => hf v) (NNReal.coe_nonneg _)
lemma weighted_add (f g : Place K G.support → ℝ) : weighted G (fun v => f v+g v)=weighted G f+weighted G g := by
  simp only [weighted,sum_add_distrib,mul_add]
lemma weighted_sub (f g : Place K G.support → ℝ) : weighted G (fun v => f v-g v)=weighted G f-weighted G g := by
  simp only [weighted,sum_sub_distrib,mul_sub]

lemma integrate (F : Data V (P×Q) → ℝ) :
    weighted G (fun v => ∫s in Icc (-radius K G.support v) (radius K G.support v), F (G.snap (v,s)))=
      mass G.support*avg G.book.levels F := by
  have hh := ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts
    G.graph G.history G.epsilon G.good G.label G.mass_pos F
  have hi := FiniteLevels.integral_eq (LevelScale.weight K)
    (fun v => -radius K G.support v) (radius K G.support)
    (fun a => F (G.snap a))
    (measurable_value G.support G.z G.w (fun pq : P×Q => G.point pq.1)
      (fun pq : P×Q => G.center pq.2) G.shifts F)
    (∑d : Data V (P×Q), |F d|) (fun a =>
      single_le_sum (s := univ) (fun d _ => abs_nonneg (F d)) (mem_univ (G.snap a)))
  exact hi.symm.trans hh

lemma height_eq (p : P) : height G p=mass G.support*avg G.book.levels (fun s => LocalProfiles.X G.book s p) :=
  integrate G (fun s => LocalProfiles.X G.book s p)
lemma error_eq (i : Bool) (a : Q×(P×P)) : error G i a=mass G.support*
    avg G.book.levels (fun s => (if i then LocalProfiles.error1 else LocalProfiles.error2) G.book s a) :=
  integrate G (fun s => (if i then LocalProfiles.error1 else LocalProfiles.error2) G.book s a)
lemma height_nonneg (p : P) : 0 ≤ height G p := weighted_nonneg G (G.height_nonneg p)
lemma error_nonneg (i : Bool) (a : Q×(P×P)) : 0 ≤ error G i a := weighted_nonneg G (G.error_nonneg i a)

lemma height_average : avg (left G.graph) (height G)=mass G.support*G.book.HP := by
  rw [show height G=(fun p => mass G.support*avg G.book.levels (fun s => LocalProfiles.X G.book s p)) from funext (height_eq G)]
  rw [avg_smul,avg_comm]
  congr 1
  exact WedgeSummary.X_average G.book

lemma wedge_height_average : avg (WedgeLaw.law G.graph) (fun a => height G a.2.1+height G a.2.2)=
    2*mass G.support*G.book.HP := by
  rw [avg_add,WedgeLaw.first_point G.graph _,WedgeLaw.second_point G.graph _,height_average]
  ring

theorem residual_budget : avg (WedgeLaw.law G.graph) (error G true) ≤
    mass G.support*(G.book.CQ+G.book.WB+4*G.book.J+4*G.book.M) := by
  rw [show error G true=(fun a => mass G.support*avg G.book.levels (fun s => LocalProfiles.error1 G.book s a)) from funext (error_eq G true)]
  rw [avg_smul,avg_comm]
  apply mul_le_mul_of_nonneg_left _ G.mass_pos.le
  exact WedgeSummary.residual_budget G.book

theorem size_budget : avg (WedgeLaw.law G.graph) (error G false) ≤
    mass G.support*(2*WedgeSummary.JW G.book+4*G.book.J+4*G.book.M) := by
  rw [show error G false=(fun a => mass G.support*avg G.book.levels (fun s => LocalProfiles.error2 G.book s a)) from funext (error_eq G false)]
  rw [avg_smul,avg_comm]
  apply mul_le_mul_of_nonneg_left _ G.mass_pos.le
  exact WedgeSummary.size_budget G.book

theorem residual (a : Q×(P×P))
    (h₁ : G.z (G.point a.2.1)-G.z (G.center a.1) ∈ G.support)
    (h₂ : G.z (G.point a.2.2)-G.z (G.center a.1) ∈ G.support) :
    l1 G (fun v => G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1-
      (G.profile a.2.1 v-G.profile a.2.2 v)) ≤ error G true a :=
  weighted_mono G (fun v => G.residual a v h₁ h₂)

theorem size (a : Q×(P×P))
    (h₁ : G.z (G.point a.2.1)-G.z (G.center a.1) ∈ G.support)
    (h₂ : G.z (G.point a.2.2)-G.z (G.center a.1) ∈ G.support) :
    height G a.2.1+height G a.2.2-error G false a ≤
      l1 G (fun v => G.threshold v a.2.1 a.1-G.threshold v a.2.2 a.1) := by
  have h := weighted_mono G (fun v => G.size a v h₁ h₂)
  rw [weighted_sub,weighted_add] at h
  exact h
end
end PlanarUnitDistances.ProfileBudget

namespace PlanarUnitDistances.RarePairBudget
open MeasureTheory Set Real FiniteLaw PlaceScore RareScore
open scoped Classical
noncomputable section
variable {A B : Type*}

lemma slot_pointwise (r : Bool) (l x y z : A×B) (b c : Bool) :
    2*RareScore.ind (exceptional r l x)-3*(RareScore.ind (exceptional r l y)+
      RareScore.ind (exceptional r l z)+RareScore.ind (¬CrossStructure.Consistent b x y)+
      RareScore.ind (¬CrossStructure.Consistent c x z)) ≤ slot r l x y z b c := by
  have h := slot_lower r l x y z b c
  have h₁ : RareScore.ind (exceptional r l x ∧ exceptional r l y) ≤ RareScore.ind (exceptional r l y) := by
    unfold RareScore.ind; split_ifs <;> simp_all
  have h₂ : RareScore.ind (exceptional r l x ∧ exceptional r l z) ≤ RareScore.ind (exceptional r l z) := by
    unfold RareScore.ind; split_ifs <;> simp_all
  linarith

def cap (ε : ℝ) (g : ℝ → ℝ) (b b' T s : ℝ) : ℝ :=
  (if g s<ε then 2 else 0)*PlaceScore.ind (Icc (b-T) b ∩ Iio b) s+
  (if 1-ε<g s then 2 else 0)*PlaceScore.ind (Icc b' (b'+T)) s

lemma cap_left {ε b b' T : ℝ} {g : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (hlo : g b<ε) (s : ℝ) :
    cap ε g b b' T s ≤ 2*PlaceScore.ind (Icc (b-T) b) s := by
  have hright : (if 1-ε<g s then (2:ℝ) else 0)*PlaceScore.ind (Icc b' (b'+T)) s=0 := by
    by_cases hs : s∈Icc b' (b'+T)
    · have hm := hg (hbb.trans hs.1)
      have hn : ¬1-ε<g s := by linarith
      simp [hn]
    · simp [PlaceScore.ind,hs]
  unfold cap
  rw [hright,add_zero]
  have hi : PlaceScore.ind (Icc (b-T) b ∩ Iio b) s ≤ PlaceScore.ind (Icc (b-T) b) s := by
    unfold PlaceScore.ind
    by_cases hs : s∈Icc (b-T) b ∩ Iio b
    · simp [hs,hs.1]
    · simp [hs,Set.indicator]; split_ifs <;> norm_num
  split_ifs <;> nlinarith [PlaceScore.ind_nonneg (Icc (b-T) b) s]

lemma cap_right {ε b b' T : ℝ} {g : ℝ → ℝ}
    (hg : Antitone g) (hlo : ε ≤ g b) (s : ℝ) :
    cap ε g b b' T s ≤ 2*PlaceScore.ind (Icc b' (b'+T)) s := by
  have hleft : (if g s<ε then (2:ℝ) else 0)*PlaceScore.ind (Icc (b-T) b ∩ Iio b) s=0 := by
    by_cases hs : s∈Icc (b-T) b ∩ Iio b
    · have hn : ¬g s<ε := not_lt.mpr (hlo.trans (hg hs.1.2))
      simp [hn]
    · simp [PlaceScore.ind,hs]
  unfold cap
  rw [hleft,zero_add]
  split_ifs <;> nlinarith [PlaceScore.ind_nonneg (Icc b' (b'+T)) s]

theorem positive_budget {ε b b' T : ℝ} {g f : ℝ → ℝ}
    (hε : ε<1/2) (hg : Antitone g) (hbb : b ≤ b') (hT : 0 ≤ T)
    (hf : Integrable f) (hcap : ∀s,f s ≤ cap ε g b b' T s) : (∫s,f s) ≤ 2*T := by
  by_cases hl : g b<ε
  · have h := integral_mono hf ((ind_Icc_integrable (b-T) b).const_mul 2)
      (fun s => (hcap s).trans (cap_left hε hg hbb hl s))
    rw [integral_const_mul,ind_Icc_integral,show b-(b-T)=T by ring,max_eq_right hT] at h
    exact h
  · have h := integral_mono hf ((ind_Icc_integrable b' (b'+T)).const_mul 2)
      (fun s => (hcap s).trans (cap_right hg (le_of_not_gt hl) s))
    rw [integral_const_mul,ind_Icc_integral,show b'+T-b'=T by ring,max_eq_right hT] at h
    exact h
end
end PlanarUnitDistances.RarePairBudget

namespace PlanarUnitDistances.RareGlobalBudget
open MeasureTheory Set Finset Real PlaceLevels BudgetPlaces LevelGeometry GlobalPairBudget
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]

theorem weighted_pair (S : Finset K) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') (hmem : differenceProduct d d'∈S)
    {ε : ℝ} (hε : ε<1/2) (g f : Place K S → ℝ → ℝ)
    (hg : ∀v,Antitone (g v)) (hf : ∀v,Integrable (f v))
    (hcap : ∀v s,f v s ≤ RarePairBudget.cap ε (g v)
      (min (threshold (av K v) d) (threshold (av K v) d'))
      (max (threshold (av K v) d) (threshold (av K v) d'))
      (alpha (av K v) d d'+allowance v) s) :
    (∑v : Place K S,((∫s,f v s)-|threshold (av K v) d-threshold (av K v) d'|)) /
      (Module.finrank ℚ K:ℝ) ≤ 2*log 2 := by
  have hb (v : Place K S) := RarePairBudget.positive_budget hε (hg v)
    (min_le_max (a:=threshold (av K v) d) (b:=threshold (av K v) d'))
    (GlobalPairBudget.thickness_nonneg v hd hd' hdd) (hf v) (hcap v)
  have hs := sum_le_sum (s:=univ) (fun v _ => sub_le_sub_right (hb v)
    |threshold (av K v) d-threshold (av K v) d'|)
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Module.finrank ℚ K))
  rw [cancellation hd hd' hdd hmem] at hh
  exact hh
end
end PlanarUnitDistances.RareGlobalBudget

namespace PlanarUnitDistances.ActualRarePair
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
open scoped Classical BigOperators
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

def positive (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x y y' : V) (e f : E) (a : Data V E) : ℝ :=
  if PlaceScore.common ε (frequency μ a) then 0 else
    LevelScores.positive ε (frequency μ a) 0 (good a) (label a) (a.2 x) (a.2 y) (a.2 y') (a.1 e) (a.1 f)
def score (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x y y' : V) (e f : E) (a : Data V E) : ℝ :=
  positive ε μ good label x y y' e f a-RareScore.ind (a.1 e≠a.1 f)

omit [Fintype V] in
lemma positive_bounds (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x y y' : V) (e f : E) (a : Data V E) :
    0≤positive ε μ good label x y y' e f a ∧ positive ε μ good label x y y' e f a≤2 := by
  unfold positive
  split_ifs
  · norm_num
  · exact LevelScores.positive_bounds _ _ _ _ _ _ _ _ _ _

lemma cap_nonneg (ε : ℝ) (g : ℝ → ℝ) (b b' T s : ℝ) :
    0≤RarePairBudget.cap ε g b b' T s := by
  unfold RarePairBudget.cap
  split_ifs <;> nlinarith [PlaceScore.ind_nonneg (Icc (b-T) b ∩ Iio b) s,
    PlaceScore.ind_nonneg (Icc b' (b'+T)) s]

lemma cap_eq {ε : ℝ} {g ρ : ℝ → ℝ} {b b' T s : ℝ}
    (hc : ¬PlaceScore.common ε (g s)) :
    PlaceScore.cap ε g ρ b b' T s=RarePairBudget.cap ε g b b' T s := by
  simp [PlaceScore.cap,PlaceScore.reward,hc,RarePairBudget.cap]

omit [Fintype V] in

theorem positive_cap (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law E)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : ε<1/2) (e f : E) (he : src e=src f)
    (hu : (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1)
    (hu' : (z (src f)-z (tgt f))*(w (src f)-w (tgt f))=1)
    (hy : z (tgt e)≠z (tgt f)) (v : Place K S) (s : ℝ) :
    positive ε μ good label (src e) (tgt e) (tgt f) e f (snapshot S z w src tgt u (v,s))≤
      RarePairBudget.cap ε (TailWindows.tail μ (fun j => threshold (av K v) (z (src j)-z (tgt j))))
        (min (threshold (av K v) (z (src e)-z (tgt e))) (threshold (av K v) (z (src f)-z (tgt f))))
        (max (threshold (av K v) (z (src e)-z (tgt e))) (threshold (av K v) (z (src f)-z (tgt f))))
        (alpha (av K v) (z (src e)-z (tgt e)) (z (src f)-z (tgt f))+LevelGeometry.allowance v) s := by
  let a := snapshot S z w src tgt u (v,s)
  by_cases hc : PlaceScore.common ε (frequency μ a)
  · unfold positive
    rw [ite_eq_left hc]
    exact cap_nonneg _ _ _ _ _ _
  · have hu'' := hu'
    rw [←he] at hu''
    have hh := LevelSlotGeometry.positive_le_cap S z w u v s ε
      (TailWindows.tail μ (fun j => threshold (av K v) (z (src j)-z (tgt j))))
      (fun _ => 0) hε (good a) (label a) (src e) (tgt e) (tgt f) hu hu'' hy
    have hcf : ¬PlaceScore.common ε (TailWindows.tail μ (fun j => threshold (av K v) (z (src j)-z (tgt j))) s) := by
      simpa only [a,ActualBudget.snapshot_frequency] using hc
    rw [cap_eq hcf] at hh
    unfold positive
    rw [ite_eq_right hc,ActualBudget.snapshot_frequency]
    convert hh using 1 <;> simp only [a,snapshot,LevelStates.bit,threshold,←he]
    rfl

theorem upper [IsGalois ℚ K] (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law E)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : ε<1/2) (e f : E) (he : src e=src f)
    (hu : (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1)
    (hu' : (z (src f)-z (tgt f))*(w (src f)-w (tgt f))=1)
    (hy : z (tgt e)≠z (tgt f))
    (hm : z (src e)-z (tgt e)∈S) (hm' : z (src f)-z (tgt f)∈S)
    (hΔ : differenceProduct (z (src e)-z (tgt e)) (z (src f)-z (tgt f))∈S) :
    (∫a,score ε μ good label (src e) (tgt e) (tgt f) e f (snapshot S z w src tgt u a)
      ∂LevelScale.measure S)≤2*log 2 := by
  let d := z (src e)-z (tgt e)
  let d' := z (src f)-z (tgt f)
  have hd : d≠0 := left_ne_zero_of_mul_eq_one hu
  have hd' : d'≠0 := left_ne_zero_of_mul_eq_one hu'
  have hdd : d≠d' := by
    dsimp only [d,d']
    rw [←he]
    exact fun h => hy (sub_right_injective h)
  let a := snapshot S z w src tgt u
  let pos := positive ε μ good label (src e) (tgt e) (tgt f) e f
  let neg : Data V E → ℝ := fun a => RareScore.ind (a.1 e≠a.1 f)
  let F : Place K S → ℝ → ℝ := fun v => (Icc (-radius K S v) (radius K S v)).indicator (fun s => pos (a (v,s)))
  have hF (v : Place K S) : Integrable (F v) :=
    (integrable_piece S z w src tgt u pos v _ _).integrable_indicator measurableSet_Icc
  have hcap (v : Place K S) (s : ℝ) : F v s≤RarePairBudget.cap ε
      (TailWindows.tail μ (fun j => threshold (av K v) (z (src j)-z (tgt j))))
      (min (threshold (av K v) d) (threshold (av K v) d'))
      (max (threshold (av K v) d) (threshold (av K v) d'))
      (alpha (av K v) d d'+LevelGeometry.allowance v) s := by
    by_cases hs : s∈Icc (-radius K S v) (radius K S v)
    · dsimp only [F]
      rw [Set.indicator_of_mem hs]
      exact positive_cap S z w src tgt u μ good label hε e f he hu hu' hy v s
    · dsimp only [F]
      rw [Set.indicator_of_notMem hs]
      exact cap_nonneg _ _ _ _ _ _
  have hb := RareGlobalBudget.weighted_pair S hd hd' hdd hΔ hε _ F
    (fun v => TailWindows.tail_antitone μ _) hF hcap
  have hbound (a : Place K S×ℝ) : |score ε μ good label (src e) (tgt e) (tgt f) e f
      (snapshot S z w src tgt u a)|≤2 := by
    have hp := positive_bounds ε μ good label (src e) (tgt e) (tgt f) e f (snapshot S z w src tgt u a)
    have hn := RareScore.ind_nonneg ((snapshot S z w src tgt u a).1 e≠(snapshot S z w src tgt u a).1 f)
    have hn' := RareScore.ind_le_one ((snapshot S z w src tgt u a).1 e≠(snapshot S z w src tgt u a).1 f)
    unfold score
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  rw [LevelScale.measure,FiniteLevels.integral_eq _ _ _ _ (measurable_value S z w src tgt u _) 2 hbound]
  have hp (v : Place K S) : (∫s in Icc (-radius K S v) (radius K S v),
      score ε μ good label (src e) (tgt e) (tgt f) e f (snapshot S z w src tgt u (v,s)))=
      (∫s,F v s)-|threshold (av K v) d-threshold (av K v) d'| := by
    change (∫s in Icc (-radius K S v) (radius K S v),pos (a (v,s))-neg (a (v,s)))=_
    rw [integral_sub (integrable_piece S z w src tgt u pos v _ _) (integrable_piece S z w src tgt u neg v _ _)]
    dsimp only [F]
    rw [integral_indicator measurableSet_Icc]
    congr 1
    exact ActualSlots.negative_integral (threshold_in_range K hm v).1 (threshold_in_range K hm v).2
      (threshold_in_range K hm' v).1 (threshold_in_range K hm' v).2
  simp_rw [hp]
  convert hb using 1
  simp only [LevelScale.weight,div_eq_mul_inv,mul_comm]
  rfl

omit [Fintype V] in
lemma lower_slot (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x y y' : V) (e f : E) (a : Data V E) :
    2*RareScore.ind (rareException ε μ good label x a)-
      3*(RareScore.ind (rareException ε μ good label y a)+RareScore.ind (rareException ε μ good label y' a)+
        RareScore.ind (¬CrossStructure.Consistent (a.1 e) (a.2 x) (a.2 y))+
        RareScore.ind (¬CrossStructure.Consistent (a.1 f) (a.2 x) (a.2 y')))-
      RareScore.ind (PlaceScore.common ε (frequency μ a))-
      RareScore.ind (¬PlaceScore.common ε (frequency μ a) ∧ ¬good a) ≤
    score ε μ good label x y y' e f a := by
  have hi := RareScore.ind_nonneg (¬CrossStructure.Consistent (a.1 e) (a.2 x) (a.2 y))
  have hi' := RareScore.ind_nonneg (¬CrossStructure.Consistent (a.1 f) (a.2 x) (a.2 y'))
  have hn := RareScore.ind_le_one (a.1 e≠a.1 f)
  by_cases hc : PlaceScore.common ε (frequency μ a)
  · simp only [score,positive,rareException,hc,not_true_eq_false,false_and,
      ite_eq_left]
    norm_num [RareScore.ind] at *
    linarith
  · by_cases hg : good a
    · have h := RarePairBudget.slot_pointwise (LevelScores.minority (frequency μ a)) (label a)
        (a.2 x) (a.2 y) (a.2 y') (a.1 e) (a.1 f)
      simpa [score,positive,LevelScores.positive,rareException,hc,hg,RareScore.slot,RareScore.ind] using h
    · simp only [score,positive,rareException,hc,hg,not_false_eq_true,true_and,false_and,and_false,
        ite_eq_right,LevelScores.positive]
      norm_num [RareScore.ind] at *
      linarith

theorem pointwise [IsGalois ℚ K] (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (μ : Law E)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    {ε : ℝ} (hε : ε<1/2) (e f : E) (he : src e=src f)
    (hu : (z (src e)-z (tgt e))*(w (src e)-w (tgt e))=1)
    (hu' : (z (src f)-z (tgt f))*(w (src f)-w (tgt f))=1)
    (hy : z (tgt e)≠z (tgt f))
    (hm : z (src e)-z (tgt e)∈S) (hm' : z (src f)-z (tgt f)∈S)
    (hΔ : differenceProduct (z (src e)-z (tgt e)) (z (src f)-z (tgt f))∈S) :
    let a := snapshot S z w src tgt u
    let X := fun x b => RareScore.ind (rareException ε μ good label x (a b))
    let I := fun j b => RareScore.ind (¬CrossStructure.Consistent ((a b).1 j) ((a b).2 (src j)) ((a b).2 (tgt j)))
    let C := fun b => RareScore.ind (PlaceScore.common ε (frequency μ (a b)))
    let B := fun b => RareScore.ind (¬PlaceScore.common ε (frequency μ (a b)) ∧ ¬good (a b))
    2*(∫b,X (src e) b ∂LevelScale.measure S) ≤
      3*((∫b,X (tgt e) b ∂LevelScale.measure S)+(∫b,X (tgt f) b ∂LevelScale.measure S)+
        (∫b,I e b ∂LevelScale.measure S)+(∫b,I f b ∂LevelScale.measure S))+
      (∫b,C b ∂LevelScale.measure S)+(∫b,B b ∂LevelScale.measure S)+2*log 2 := by
  dsimp only
  let a := snapshot S z w src tgt u
  let X := fun x b => RareScore.ind (rareException ε μ good label x (a b))
  let I := fun j b => RareScore.ind (¬CrossStructure.Consistent ((a b).1 j) ((a b).2 (src j)) ((a b).2 (tgt j)))
  let C := fun b => RareScore.ind (PlaceScore.common ε (frequency μ (a b)))
  let B := fun b => RareScore.ind (¬PlaceScore.common ε (frequency μ (a b)) ∧ ¬good (a b))
  have hX (x) : Integrable (X x) (LevelScale.measure S) :=
    integrable_value S z w src tgt u (fun b => RareScore.ind (rareException ε μ good label x b))
  have hI (j) : Integrable (I j) (LevelScale.measure S) :=
    integrable_value S z w src tgt u (fun b => RareScore.ind (¬CrossStructure.Consistent (b.1 j) (b.2 (src j)) (b.2 (tgt j))))
  have hC : Integrable C (LevelScale.measure S) :=
    integrable_value S z w src tgt u (fun b => RareScore.ind (PlaceScore.common ε (frequency μ b)))
  have hB : Integrable B (LevelScale.measure S) :=
    integrable_value S z w src tgt u (fun b => RareScore.ind (¬PlaceScore.common ε (frequency μ b) ∧ ¬good b))
  have hsum := (((hX (tgt e)).add (hX (tgt f))).add (hI e)).add (hI f)
  have hlow := ((((hX (src e)).const_mul 2).sub (hsum.const_mul 3)).sub hC).sub hB
  have hlo := integral_mono hlow
    (integrable_value S z w src tgt u (score ε μ good label (src e) (tgt e) (tgt f) e f))
    (fun b => by simpa only [Pi.sub_apply,Pi.add_apply,X,I,C,B,←he] using lower_slot ε μ good label (src e) (tgt e) (tgt f) e f (a b))
  simp only [Pi.sub_apply,Pi.add_apply] at hlo
  rw [integral_sub _ hB,integral_sub _ hC,integral_sub,integral_const_mul,integral_const_mul,
    integral_add,integral_add,integral_add] at hlo
  · have hup := upper S z w src tgt u μ good label hε e f he hu hu' hy hm hm' hΔ
    change 2*(∫b,X (src e) b ∂LevelScale.measure S) ≤
      3*((∫b,X (tgt e) b ∂LevelScale.measure S)+(∫b,X (tgt f) b ∂LevelScale.measure S)+
        (∫b,I e b ∂LevelScale.measure S)+(∫b,I f b ∂LevelScale.measure S))+
      (∫b,C b ∂LevelScale.measure S)+(∫b,B b ∂LevelScale.measure S)+2*log 2
    linarith
  all_goals fun_prop
end
end PlanarUnitDistances.ActualRarePair

namespace PlanarUnitDistances.ActualHeights
open MeasureTheory FiniteLaw FiniteStarCoupling ActualProfiles ActualScoreBook LevelSnapshot
  ProfileBudget ScoreBook RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)
def center (q : Q) : ℝ := mass G.support*avg G.book.levels
  (fun d => if G.book.R d then ind (LocalProfiles.exceptional G.book d (G.book.center d q)) else 0)
def mistake (p : P) (q : Q) : ℝ := mass G.support*avg G.book.levels
  (fun d => ind (¬CrossStructure.Consistent (G.book.bit d p q) (G.book.point d p) (G.book.center d q)))
lemma center_nonneg (q : Q) : 0 ≤ center G q := by
  apply mul_nonneg G.mass_pos.le
  apply avg_nonneg
  intro d
  unfold ind
  split_ifs <;> norm_num
lemma mistake_nonneg (p : P) (q : Q) : 0 ≤ mistake G p q := by
  apply mul_nonneg G.mass_pos.le
  apply avg_nonneg
  intro d
  unfold ind
  split_ifs <;> norm_num
lemma center_average : avg (right G.graph) (center G)=mass G.support*G.book.HQ := by
  unfold center
  rw [avg_smul,avg_comm]
  congr 1
  unfold Book.HQ cut
  apply avg_congr
  intro d
  by_cases hd : G.book.R d
  · simp only [hd,↓reduceIte]
    rfl
  · simp only [hd,↓reduceIte,avg_const]
lemma mistake_average : avg G.graph (fun pq => mistake G pq.1 pq.2)=mass G.support*G.book.M := by
  unfold mistake
  rw [avg_smul,avg_comm]
  rfl
lemma point_integral (p : P) :
    (∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.point p) (G.snap b))
      ∂LevelScale.measure G.support)=height G p := by
  rw [height_eq]
  have hh := ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.point p) d))
  unfold Input.snap
  rw [hh]
  congr 1
  apply avg_congr
  intro d
  simp only [ActualSlots.rareException,LocalProfiles.X,LocalProfiles.exceptional,LocalProfiles.rareBit,
    ActualSlots.frequency,Input.book,make,Book.R,Book.C,GlobalScores.common,RareRows.frequency]
  unfold ind
  split_ifs <;> simp_all
lemma center_integral (q : Q) :
    (∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.center q) (G.snap b))
      ∂LevelScale.measure G.support)=center G q := by
  have hh := ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.center q) d))
  unfold Input.snap
  rw [hh]
  unfold center
  congr 1
  apply avg_congr
  intro d
  simp only [ActualSlots.rareException,LocalProfiles.exceptional,LocalProfiles.rareBit,
    ActualSlots.frequency,Input.book,make,Book.R,Book.C,GlobalScores.common,RareRows.frequency]
  unfold ind
  split_ifs <;> simp_all
lemma inconsistent_integral (p : P) (q : Q) :
    (∫b,ind (¬CrossStructure.Consistent ((G.snap b).1 (p,q)) ((G.snap b).2 (G.point p))
      ((G.snap b).2 (G.center q))) ∂LevelScale.measure G.support)=mistake G p q :=
  ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (¬CrossStructure.Consistent (d.1 (p,q)) (d.2 (G.point p)) (d.2 (G.center q))))
lemma common_integral :
    (∫b,ind (PlaceScore.common G.epsilon (ActualSlots.frequency G.graph (G.snap b)))
      ∂LevelScale.measure G.support)=mass G.support*G.book.WC :=
  ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (PlaceScore.common G.epsilon (ActualSlots.frequency G.graph d)))
lemma bad_integral :
    (∫b,ind (¬PlaceScore.common G.epsilon (ActualSlots.frequency G.graph (G.snap b)) ∧ ¬G.good (G.snap b))
      ∂LevelScale.measure G.support)=mass G.support*G.book.WB :=
  ActualScoreBook.average G.support G.z G.w G.point G.center G.shifts G.graph
    G.history G.epsilon G.good G.label G.mass_pos
    (fun d => ind (¬PlaceScore.common G.epsilon (ActualSlots.frequency G.graph d) ∧ ¬G.good d))
theorem pointwise [IsGalois ℚ K] (hε : G.epsilon<1/2) (p : P) (q r : Q)
    (hu : (G.z (G.point p)-G.z (G.center q))*(G.w (G.point p)-G.w (G.center q))=1)
    (hur : (G.z (G.point p)-G.z (G.center r))*(G.w (G.point p)-G.w (G.center r))=1)
    (hy : G.z (G.center q)≠G.z (G.center r))
    (hm : G.z (G.point p)-G.z (G.center q)∈G.support)
    (hmr : G.z (G.point p)-G.z (G.center r)∈G.support)
    (hΔ : BudgetPlaces.differenceProduct (G.z (G.point p)-G.z (G.center q))
      (G.z (G.point p)-G.z (G.center r))∈G.support) :
    2*height G p≤3*(center G q+center G r+mistake G p q+mistake G p r)+
      mass G.support*(G.book.WC+G.book.WB)+2*Real.log 2 := by
  have hh := ActualRarePair.pointwise G.support G.z G.w (fun pq : P×Q => G.point pq.1)
    (fun pq : P×Q => G.center pq.2) G.shifts G.graph G.good G.label hε (p,q) (p,r)
    rfl hu hur hy hm hmr hΔ
  dsimp only at hh
  change 2*(∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.point p) (G.snap b))
      ∂LevelScale.measure G.support) ≤
    3*((∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.center q) (G.snap b)) ∂LevelScale.measure G.support)+
       (∫b,ind (ActualSlots.rareException G.epsilon G.graph G.good G.label (G.center r) (G.snap b)) ∂LevelScale.measure G.support)+
       (∫b,ind (¬CrossStructure.Consistent ((G.snap b).1 (p,q)) ((G.snap b).2 (G.point p)) ((G.snap b).2 (G.center q))) ∂LevelScale.measure G.support)+
       (∫b,ind (¬CrossStructure.Consistent ((G.snap b).1 (p,r)) ((G.snap b).2 (G.point p)) ((G.snap b).2 (G.center r))) ∂LevelScale.measure G.support))+
    (∫b,ind (PlaceScore.common G.epsilon (ActualSlots.frequency G.graph (G.snap b))) ∂LevelScale.measure G.support)+
    (∫b,ind (¬PlaceScore.common G.epsilon (ActualSlots.frequency G.graph (G.snap b)) ∧ ¬G.good (G.snap b)) ∂LevelScale.measure G.support)+2*Real.log 2 at hh
  rw [point_integral,center_integral,center_integral,inconsistent_integral,inconsistent_integral,
    common_integral,bad_integral] at hh
  linarith
end
end PlanarUnitDistances.ActualHeights

end OAI
