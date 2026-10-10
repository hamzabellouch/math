import OAI.Geometry.UnitDistances.RareEvents

namespace OAI

namespace PlanarUnitDistances.GlobalScores
open FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareRows LevelScores RareScore RareMoments
open scoped Classical
noncomputable section
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype I]

def common (ε : ℝ) (π : Law (P×Q)) (b : D → P → Q → Bool) (s : D) : Prop :=
  PlaceScore.common ε (event π (fun pq => b s pq.1 pq.2=true))

def bad (c g : D → Prop) (s : D) : Prop := ¬c s ∧ ¬g s

theorem common_lower (σ : Law D) (π : Law (P×Q)) (h : P → H)
    (b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A)
    (hμ : ∀p,0<(left π).val p) (hκ : ∀q,0<(right π).val q)
    {ζ η : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2)
    (ε : ℝ) (g : D → Prop) (l : D → A×A) :
    let c := common ε π b
    let R := fun s => ¬c s ∧ g s
    let a := templateLaw (I := I) π h
    let CT := cut σ c (fun s => avg (templates π a) (fun θ => VP (slice π a θ) (b s)))
    let CQ := cut σ c (fun s => VQ π (b s))
    (CT+CQ)/80000 ≤
      avg σ (fun s => scoreT ε (frequency π (b s)) π a (b s) (x s) (y s) (g s) (l s))+
      avg σ (fun s => scoreQ ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s))+
      12*avg σ (fun s => RareLabels.error π (b s) (x s) (y s))+
      (12*(Fintype.card I:ℝ)/ζ)*cut σ c (fun s => predictionError π h (x s) (y s))+
      (12*(samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η))*event σ c+
      8*cut σ R (fun s => RareMoments.joint π (b s) (x s) (y s) (l s))+2*event σ (bad c g) := by
  dsimp only
  let c := common ε π b
  let R := fun s => ¬c s ∧ g s
  let m := fun s => RareLabels.error π (b s) (x s) (y s)
  let J := fun s => RareMoments.joint π (b s) (x s) (y s) (l s)
  let pe := fun s => predictionError π h (x s) (y s)
  let e := samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η
  have he : avg σ (fun s => if c s then 12*(m s+((Fintype.card I:ℝ)/ζ)*pe s+e)
      else if g s then 8*J s+12*m s else 2) ≤
      12*avg σ m+(12*(Fintype.card I:ℝ)/ζ)*cut σ c pe+12*e*event σ c+
      8*cut σ R J+2*event σ (bad c g) := by
    have hh := avg_mono σ (f := fun s => if c s then 12*(m s+((Fintype.card I:ℝ)/ζ)*pe s+e)
      else if g s then 8*J s+12*m s else 2)
      (g := fun s => 12*m s+(12*(Fintype.card I:ℝ)/ζ)*(if c s then pe s else 0)+
        12*e*(if c s then 1 else 0)+8*(if R s then J s else 0)+2*(if bad c g s then 1 else 0)) (by
        intro s
        have hm : 0 ≤ m s := event_nonneg _ _
        by_cases hc : c s <;> by_cases hg : g s <;>
          simp only [hc,hg,R,bad,not_true_eq_false,not_false_eq_true,and_self,and_false,and_true,ite_true,ite_false,div_eq_mul_inv] <;> nlinarith)
    simp only [avg_add,avg_smul] at hh
    unfold cut event
    convert hh using 1; congr!
  have hbal := CommonRareScore.balanced_average (I := I) σ π h b x y hμ hκ hζ hk hI hη hη' ε g l
  have hl : avg σ (fun s => if c s then
      (avg (templates π (templateLaw (I := I) π h)) (fun θ => VP (slice π (templateLaw (I := I) π h) θ) (b s))+VQ π (b s))/80000 else 0)=
      (cut σ c (fun s => avg (templates π (templateLaw (I := I) π h)) (fun θ => VP (slice π (templateLaw (I := I) π h) θ) (b s)))+
      cut σ c (fun s => VQ π (b s)))/80000 := by
    change cut σ c (fun s => _/80000)=_
    simp_rw [div_eq_mul_inv,mul_comm _ (80000:ℝ)⁻¹]
    rw [cut_smul,cut_add]
  dsimp [c,common] at hl
  change _ ≤ _ at hbal
  change _ ≤ _ at he
  erw [hl] at hbal
  dsimp [c,R,m,J,pe,e,frequency,common,RareLabels.error,RareMoments.joint] at he ⊢
  simp only [add_assoc] at he hbal ⊢
  linarith

omit [Fintype A] in
lemma center_score_lower (π : Law (P×Q)) (b : P → Q → Bool) (x : P → A×A) :
    -VQ π b ≤ DQ π b x := by
  have h := avg_mono (right π) (fun q => StarScore.score_lower (col π q) (fun p => b p q) x)
  simpa only [avg_neg,VQ,DQ] using h

omit [Fintype A] in

theorem center_lower (σ : Law D) (π : Law (P×Q)) (b : D → P → Q → Bool)
    (x : D → P → A×A) (y : D → Q → A×A) (ε : ℝ) (g : D → Prop) (l : D → A×A) :
    let c := common ε π b
    let R := fun s => ¬c s ∧ g s
    2*cut σ R (fun s => hq π (b s) (y s) (l s))-2*cut σ R (fun s => hp π (b s) (x s) (l s))-
      4*cut σ R (fun s => RareMoments.joint π (b s) (x s) (y s) (l s))-
      6*avg σ (fun s => RareLabels.error π (b s) (x s) (y s))-
      cut σ c (fun s => VQ π (b s))-event σ (bad c g) ≤
      avg σ (fun s => scoreQ ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)) := by
  dsimp only
  let c := common ε π b
  let R := fun s => ¬c s ∧ g s
  have hh := avg_mono σ (f := fun s => 2*(if R s then hq π (b s) (y s) (l s) else 0)-
    2*(if R s then hp π (b s) (x s) (l s) else 0)-4*(if R s then RareMoments.joint π (b s) (x s) (y s) (l s) else 0)-
    6*RareLabels.error π (b s) (x s) (y s)-(if c s then VQ π (b s) else 0)-(if bad c g s then 1 else 0))
    (g := fun s => scoreQ ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)) (by
      intro s
      have hm := event_nonneg π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))
      by_cases hc : c s
      · have hs := center_score_lower π (b s) (x s)
        rw [common_Q π (b s) (x s) (y s) (g s) (l s) (show PlaceScore.common ε (frequency π (b s)) from hc)]
        simp only [R,bad,hc,not_true_eq_false,false_and,ite_false,ite_true]
        dsimp [RareLabels.error] at *; linarith
      · by_cases hg : g s
        · have hs := rare_Q π (b s) (x s) (y s) (g s) (l s) hc hg
          simpa only [R,bad,hc,hg,not_false_eq_true,not_true_eq_false,and_self,and_false,ite_true,ite_false,sub_zero,hq,hp,RareMoments.joint,RareLabels.error,frequency] using hs
        · have hs := scoreQ_lower ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)
          simp only [R,bad,hc,hg,not_false_eq_true,true_and,ite_true,ite_false] at hs ⊢
          dsimp [RareLabels.error] at *; linarith)
  simpa only [avg_sub,avg_smul,cut,event] using hh
end
end PlanarUnitDistances.GlobalScores

namespace PlanarUnitDistances.GlobalMarginal
open FiniteLaw FiniteStarCoupling CommonTemplate RareRows LevelScores RareScore RareMoments GlobalScores
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A]

omit [Fintype H] in

theorem point_lower (σ : Law D) (π : Law (P×Q)) (h : P → H)
    (b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A)
    {δ : ℝ} (hδ : 0<δ) (ε : ℝ) (g : D → Prop) (l : D → A×A) :
    let c := common ε π b
    let R := fun s => ¬c s ∧ g s
    cut σ c (fun s => VP π (b s))/80000 ≤
      avg σ (fun s => scoreP ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s))+
      cut σ c (fun s => avg (left π) (fun p => FiniteMarginalScore.tau (posteriorState π h (x s) (h p))))+
      2*cut σ R (fun s => hq π (b s) (y s) (l s))+
      4*cut σ R (fun s => RareMoments.joint π (b s) (x s) (y s) (l s))+
      26*avg σ (fun s => RareLabels.error π (b s) (x s) (y s))+
      (20/δ)*cut σ c (fun s => predictionError π h (x s) (y s))+
      (20*δ)*event σ c+event σ (GlobalScores.bad c g) := by
  dsimp only
  let c := common ε π b
  let R := fun s => ¬c s ∧ g s
  have hh := avg_mono σ (f := fun s => if c s then VP π (b s)/80000 else 0)
    (g := fun s => scoreP ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)+
      (if c s then avg (left π) (fun p => FiniteMarginalScore.tau (posteriorState π h (x s) (h p))) else 0)+
      2*(if R s then hq π (b s) (y s) (l s) else 0)+
      4*(if R s then RareMoments.joint π (b s) (x s) (y s) (l s) else 0)+
      26*RareLabels.error π (b s) (x s) (y s)+
      (20/δ)*(if c s then predictionError π h (x s) (y s) else 0)+
      (20*δ)*(if c s then 1 else 0)+(if GlobalScores.bad c g s then 1 else 0)) (by
      intro s
      have hm := event_nonneg π (fun pq => ¬CrossStructure.Consistent (b s pq.1 pq.2) (x s pq.1) (y s pq.2))
      by_cases hc : c s
      · have hs := marginal_score π h (b s) (x s) (y s) hδ
        rw [common_P π (b s) (x s) (y s) (g s) (l s) (show PlaceScore.common ε (frequency π (b s)) from hc)]
        simp only [R,GlobalScores.bad,hc,not_true_eq_false,false_and,ite_false,ite_true]
        dsimp only [RareLabels.error]
        simp only [div_eq_mul_inv] at hs ⊢
        nlinarith
      · by_cases hg : g s
        · have hs := rare_P π (b s) (x s) (y s) (g s) (l s) hc hg
          have hpt : 0 ≤ hp π (b s) (x s) (l s) := event_nonneg _ _
          simp only [R,GlobalScores.bad,hc,hg,not_false_eq_true,not_true_eq_false,and_self,and_false,ite_true,ite_false] at hs ⊢
          dsimp only [RareLabels.error,RareMoments.joint,hq,hp,frequency] at hs hpt ⊢
          linarith
        · have hs := scoreP_lower ε (frequency π (b s)) π (b s) (x s) (y s) (g s) (l s)
          simp only [R,GlobalScores.bad,hc,hg,not_false_eq_true,true_and,ite_true,ite_false] at hs ⊢
          dsimp only [RareLabels.error] at *
          linarith)
  have hl : avg σ (fun s => if c s then VP π (b s)/80000 else 0)=
      cut σ c (fun s => VP π (b s))/80000 := by
    change cut σ c (fun s => VP π (b s)/80000)=_
    simp_rw [div_eq_mul_inv,mul_comm _ (80000:ℝ)⁻¹]
    rw [cut_smul]
  rw [hl] at hh
  simp only [avg_add,avg_smul] at hh
  dsimp only [c,R] at hh
  simp only [cut,event] at hh ⊢
  convert hh using 1

omit [Fintype A] in

theorem scale_lower (σ : Law D) (π : Law (P×Q))
    (b : D → P → Q → Bool) (x : D → P → A×A) (y : D → Q → A×A)
    (ε C : ℝ) (g : D → Prop) (l : D → A×A)
    (hstable : ∀s,common ε π b s → RareLabels.minorityMass π (b s) ≤ C*(VP π (b s)+VQ π (b s)))
    (hrare : ∀s,¬common ε π b s → g s → RareLabels.minorityMass π (b s) ≤
      hp π (b s) (x s) (l s)+hq π (b s) (y s) (l s)+RareLabels.error π (b s) (x s) (y s)) :
    let c := common ε π b
    let R := fun s => ¬c s ∧ g s
    avg σ (fun s => RareLabels.minorityMass π (b s)) ≤
      C*(cut σ c (fun s => VP π (b s))+cut σ c (fun s => VQ π (b s)))+
      cut σ R (fun s => hp π (b s) (x s) (l s))+cut σ R (fun s => hq π (b s) (y s) (l s))+
      avg σ (fun s => RareLabels.error π (b s) (x s) (y s))+event σ (GlobalScores.bad c g)/2 := by
  dsimp only
  let c := common ε π b
  let R := fun s => ¬c s ∧ g s
  have hh := avg_mono σ (f := fun s => RareLabels.minorityMass π (b s))
    (g := fun s => C*((if c s then VP π (b s) else 0)+(if c s then VQ π (b s) else 0))+
      (if R s then hp π (b s) (x s) (l s) else 0)+(if R s then hq π (b s) (y s) (l s) else 0)+
      RareLabels.error π (b s) (x s) (y s)+(1/2)*(if GlobalScores.bad c g s then 1 else 0)) (by
      intro s
      have hm : 0 ≤ RareLabels.error π (b s) (x s) (y s) := event_nonneg _ _
      by_cases hc : c s <;> by_cases hg : g s <;>
        simp only [R,GlobalScores.bad,hc,hg,not_true_eq_false,not_false_eq_true,and_self,and_false,and_true,ite_true,ite_false]
      · linarith [hstable s hc]
      · linarith [hstable s hc]
      · simpa using hrare s hc hg
      · linarith [LevelBookkeeping.minority_le_half π (b s)])
  simp only [avg_add,avg_smul] at hh
  dsimp only [c,R] at hh
  simp only [cut,event,div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹,mul_one] at hh ⊢
  convert hh using 1
end
end PlanarUnitDistances.GlobalMarginal

namespace PlanarUnitDistances.ScoreBook
open FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareRows RareMoments GlobalScores
open scoped Classical
noncomputable section

structure Book (D P Q H A : Type) [Fintype D] [Fintype P] [Fintype Q] where
  levels : Law D
  graph : Law (P×Q)
  bit : D → P → Q → Bool
  point : D → P → A×A
  center : D → Q → A×A
  history : P → H
  epsilon : ℝ
  good : D → Prop
  label : D → A×A

namespace Book
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype I]

def C (B : Book D P Q H A) : D → Prop := common B.epsilon B.graph B.bit
def R (B : Book D P Q H A) : D → Prop := fun s => ¬B.C s ∧ B.good s
def S (B : Book D P Q H A) := avg B.levels (fun s => RareLabels.minorityMass B.graph (B.bit s))
def M (B : Book D P Q H A) := avg B.levels (fun s => RareLabels.error B.graph (B.bit s) (B.point s) (B.center s))
def WC (B : Book D P Q H A) := event B.levels B.C
def WB (B : Book D P Q H A) := event B.levels (GlobalScores.bad B.C B.good)
def HP (B : Book D P Q H A) := cut B.levels B.R (fun s => hp B.graph (B.bit s) (B.point s) (B.label s))
def HQ (B : Book D P Q H A) := cut B.levels B.R (fun s => hq B.graph (B.bit s) (B.center s) (B.label s))
def J (B : Book D P Q H A) := cut B.levels B.R (fun s => RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s))
def EP (B : Book D P Q H A) := cut B.levels B.C (fun s => predictionError B.graph B.history (B.point s) (B.center s))
def CP (B : Book D P Q H A) := cut B.levels B.C (fun s => VP B.graph (B.bit s))
def CQ (B : Book D P Q H A) := cut B.levels B.C (fun s => VQ B.graph (B.bit s))
def CT (B : Book D P Q H A) := cut B.levels B.C (fun s => avg
  (templates B.graph (templateLaw (I := I) B.graph B.history))
  (fun θ => VP (slice B.graph (templateLaw (I := I) B.graph B.history) θ) (B.bit s)))
def DP (B : Book D P Q H A) := avg B.levels (fun s => scoreP B.epsilon (frequency B.graph (B.bit s))
  B.graph (B.bit s) (B.point s) (B.center s) (B.good s) (B.label s))
def DQ (B : Book D P Q H A) := avg B.levels (fun s => scoreQ B.epsilon (frequency B.graph (B.bit s))
  B.graph (B.bit s) (B.point s) (B.center s) (B.good s) (B.label s))
def DT (B : Book D P Q H A) := avg B.levels (fun s => scoreT B.epsilon (frequency B.graph (B.bit s))
  B.graph (templateLaw (I := I) B.graph B.history) (B.bit s) (B.point s) (B.center s) (B.good s) (B.label s))
def T (B : Book D P Q H A) := cut B.levels B.C (fun s => avg (left B.graph)
  (fun p => FiniteMarginalScore.tau (posteriorState B.graph B.history (B.point s) (B.history p))))

omit [Fintype A] [Fintype H] [Fintype I] in
lemma nonneg (B : Book D P Q H A) : 0 ≤ B.S ∧ 0 ≤ B.M ∧ 0 ≤ B.HP ∧ 0 ≤ B.HQ ∧
    0 ≤ B.CP ∧ 0 ≤ B.CQ ∧ 0 ≤ B.J ∧ 0 ≤ B.WC ∧ 0 ≤ B.WB := by
  refine ⟨avg_nonneg _ (fun _ => LevelBookkeeping.minority_nonneg _ _),avg_nonneg _ (fun _ => event_nonneg _ _),
    cut_nonneg _ _ _ (fun _ => event_nonneg _ _),cut_nonneg _ _ _ (fun _ => event_nonneg _ _),
    cut_nonneg _ _ _ (fun _ => avg_nonneg _ (fun _ => StarScore.variation_nonneg _ _)),
    cut_nonneg _ _ _ (fun _ => avg_nonneg _ (fun _ => StarScore.variation_nonneg _ _)),
    cut_nonneg _ _ _ (fun _ => event_nonneg _ _),event_nonneg _ _,event_nonneg _ _⟩
omit [Fintype A] in
lemma CT_nonneg (B : Book D P Q H A) : 0 ≤ CT (I := I) B :=
  cut_nonneg _ _ _ (fun _ => avg_nonneg _ (fun _ => avg_nonneg _ (fun _ => StarScore.variation_nonneg _ _)))

theorem common_lower (B : Book D P Q H A)
    (hμ : ∀p,0<(left B.graph).val p) (hκ : ∀q,0<(right B.graph).val q)
    {ζ η : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2) :
    (CT (I := I) B+B.CQ)/80000 ≤ DT (I := I) B+B.DQ+12*B.M+
      (12*(Fintype.card I:ℝ)/ζ)*B.EP+
      (12*(CommonTemplate.samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η))*B.WC+
      8*B.J+2*B.WB := by
  exact GlobalScores.common_lower B.levels B.graph B.history B.bit B.point B.center hμ hκ hζ hk hI hη hη'
    B.epsilon B.good B.label

omit [Fintype A] [Fintype H] [Fintype I] in
lemma center_lower (B : Book D P Q H A) :
    2*B.HQ-2*B.HP-4*B.J-6*B.M-B.CQ-B.WB ≤ B.DQ :=
  GlobalScores.center_lower B.levels B.graph B.bit B.point B.center B.epsilon B.good B.label

omit [Fintype H] [Fintype I] in
lemma point_lower (B : Book D P Q H A) {δ : ℝ} (hδ : 0<δ) :
    B.CP/80000 ≤ B.DP+B.T+2*B.HQ+4*B.J+26*B.M+(20/δ)*B.EP+(20*δ)*B.WC+B.WB :=
  GlobalMarginal.point_lower B.levels B.graph B.history B.bit B.point B.center hδ B.epsilon B.good B.label

omit [Fintype A] [Fintype H] [Fintype I] in
lemma scale_lower (B : Book D P Q H A) (L : ℝ)
    (hstable : ∀s,B.C s → RareLabels.minorityMass B.graph (B.bit s) ≤ L*(VP B.graph (B.bit s)+VQ B.graph (B.bit s)))
    (hrare : ∀s,¬B.C s → B.good s → RareLabels.minorityMass B.graph (B.bit s) ≤
      hp B.graph (B.bit s) (B.point s) (B.label s)+hq B.graph (B.bit s) (B.center s) (B.label s)+
        RareLabels.error B.graph (B.bit s) (B.point s) (B.center s)) :
    B.S ≤ L*(B.CP+B.CQ)+B.HP+B.HQ+B.M+B.WB/2 :=
  GlobalMarginal.scale_lower B.levels B.graph B.bit B.point B.center B.epsilon L B.good B.label hstable hrare
end Book
end
end PlanarUnitDistances.ScoreBook

namespace PlanarUnitDistances.ScoreCoercivity
noncomputable section

theorem from_scores {S HP HQ CP CQ CT DP DQ DT T E L : ℝ}
    (hE : 0 ≤ E) (hHP : 0 ≤ HP) (hCT : 0 ≤ CT) (hL : 0 ≤ L)
    (hcommon : (CT+CQ)/80000 ≤ DT+DQ+E)
    (hDT : DT ≤ CT/20000000+E) (hDQ : DQ ≤ CQ/20000000+E)
    (hcenter : 2*HQ-2*HP-CQ-E ≤ DQ)
    (hpoint : CP/80000 ≤ DP+T+2*HQ+E)
    (hDP : DP ≤ CP/20000000+E) (hT : T ≤ 2*HP+E)
    (hscale : S ≤ L*(CP+CQ)+HP+HQ+E) :
    CQ ≤ 250000*E ∧ HQ ≤ HP+130000*E ∧
      S ≤ (400000*L+2)*HP+(23000000000*L+130001)*E := by
  have hc : CT+CQ ≤ 250000*E := by linarith
  have hq : CQ ≤ 250000*E := by linarith
  have hQ : HQ ≤ HP+130000*E := by linarith
  have hp : CP ≤ 400000*HP+22000000000*E := by linarith
  refine ⟨hq,hQ,?_⟩
  have hsum : CP+CQ ≤ 400000*HP+23000000000*E := by linarith
  have hh := mul_le_mul_of_nonneg_left hsum hL
  nlinarith

theorem positive {S HP E L : ℝ} (hL : 0 ≤ L)
    (hscale : S ≤ (400000*L+2)*HP+(23000000000*L+130001)*E)
    (hsmall : E ≤ S/(2*(23000000000*L+130001))) :
    S/(2*(400000*L+2)) ≤ HP := by
  have ha : 0 < 400000*L+2 := by positivity
  have hb : 0 < 23000000000*L+130001 := by positivity
  have hh := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hb)).mp hsmall
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) ha)).mpr
  nlinarith
end
end PlanarUnitDistances.ScoreCoercivity

namespace PlanarUnitDistances.BookCoercivity
open FiniteLaw ScoreBook FiniteStarCoupling RareMoments
open scoped Classical
noncomputable section
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q]
  [Fintype H] [Fintype A] [Fintype I]

def commonLoss (B : Book D P Q H A) (ζ η : ℝ) : ℝ :=
  12*B.M+(12*(Fintype.card I:ℝ)/ζ)*B.EP+
    (12*(CommonTemplate.samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η))*B.WC+
    8*B.J+2*B.WB
omit [Fintype I] in
def centerLoss (B : Book D P Q H A) : ℝ := 4*B.J+6*B.M+B.WB
omit [Fintype I] in
def pointLoss (B : Book D P Q H A) (δ : ℝ) : ℝ :=
  4*B.J+26*B.M+(20/δ)*B.EP+(20*δ)*B.WC+B.WB
omit [Fintype I] in
def scaleLoss (B : Book D P Q H A) : ℝ := B.M+B.WB/2

def loss (B : Book D P Q H A) (ζ η δ eP eQ eT ePred : ℝ) : ℝ :=
  |commonLoss (I := I) B ζ η|+|centerLoss B|+|pointLoss B δ|+|scaleLoss B|+
    |eP|+|eQ|+|eT|+|ePred|

omit [Fintype H] in
lemma loss_bounds (B : Book D P Q H A) (ζ η δ eP eQ eT ePred : ℝ) :
    let E := loss (I := I) B ζ η δ eP eQ eT ePred
    0 ≤ E ∧ commonLoss (I := I) B ζ η ≤ E ∧ centerLoss B ≤ E ∧
      pointLoss B δ ≤ E ∧ scaleLoss B ≤ E ∧ eP ≤ E ∧ eQ ≤ E ∧ eT ≤ E ∧ ePred ≤ E := by
  dsimp only [loss]
  have h0 := abs_nonneg (commonLoss (I := I) B ζ η)
  have h1 := abs_nonneg (centerLoss B)
  have h2 := abs_nonneg (pointLoss B δ)
  have h3 := abs_nonneg (scaleLoss B)
  have h4 := abs_nonneg eP
  have h5 := abs_nonneg eQ
  have h6 := abs_nonneg eT
  have h7 := abs_nonneg ePred
  have l0 := le_abs_self (commonLoss (I := I) B ζ η)
  have l1 := le_abs_self (centerLoss B)
  have l2 := le_abs_self (pointLoss B δ)
  have l3 := le_abs_self (scaleLoss B)
  have l4 := le_abs_self eP
  have l5 := le_abs_self eQ
  have l6 := le_abs_self eT
  have l7 := le_abs_self ePred
  refine ⟨by positivity,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    linarith only [h0,h1,h2,h3,h4,h5,h6,h7,l0,l1,l2,l3,l4,l5,l6,l7]

theorem coercivity (B : Book D P Q H A)
    (hμ : ∀p,0<(left B.graph).val p) (hκ : ∀q,0<(right B.graph).val q)
    {ζ η δ L eP eQ eT ePred : ℝ} (hζ : 0<ζ) (hk : (Fintype.card I:ℝ)*ζ<1)
    (hI : 0<Fintype.card I) (hη : 0<η) (hη' : η<1/2) (hδ : 0<δ) (hL : 0 ≤ L)
    (hstable : ∀s,B.C s → RareLabels.minorityMass B.graph (B.bit s) ≤ L*(VP B.graph (B.bit s)+VQ B.graph (B.bit s)))
    (hrare : ∀s,¬B.C s → B.good s → RareLabels.minorityMass B.graph (B.bit s) ≤
      hp B.graph (B.bit s) (B.point s) (B.label s)+hq B.graph (B.bit s) (B.center s) (B.label s)+
        RareLabels.error B.graph (B.bit s) (B.point s) (B.center s))
    (hDP : B.DP ≤ B.CP/20000000+eP) (hDQ : B.DQ ≤ B.CQ/20000000+eQ)
    (hDT : Book.DT (I := I) B ≤ Book.CT (I := I) B/20000000+eT)
    (hT : B.T ≤ 2*B.HP+ePred) :
    B.S ≤ (400000*L+2)*B.HP+(23000000000*L+130001)*loss (I := I) B ζ η δ eP eQ eT ePred := by
  obtain ⟨hE,h0,h1,h2,h3,h4,h5,h6,h7⟩ := loss_bounds (I := I) B ζ η δ eP eQ eT ePred
  have hc := B.common_lower (I := I) hμ hκ hζ hk hI hη hη'
  have hq := B.center_lower
  have hp := B.point_lower hδ
  have hs := B.scale_lower L hstable hrare
  have hnn := B.nonneg
  have hct := B.CT_nonneg (I := I)
  dsimp only [commonLoss,centerLoss,pointLoss,scaleLoss] at h0 h1 h2 h3
  exact (ScoreCoercivity.from_scores (S := B.S) (HP := B.HP) (HQ := B.HQ)
    (CP := B.CP) (CQ := B.CQ) (CT := Book.CT (I := I) B)
    (DP := B.DP) (DQ := B.DQ) (DT := Book.DT (I := I) B) (T := B.T) hE hnn.2.2.1 hct hL
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith)).2.2
end
end PlanarUnitDistances.BookCoercivity

namespace PlanarUnitDistances.LevelSnapshot
open MeasureTheory Set Finset FiniteLaw LevelStates PlaceLevels
open scoped Classical
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

abbrev Data (V E : Type*) := (E → Bool)×(V → ((V → Bool)×(V → Bool)))

def snapshot (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S×ℝ) : Data V E :=
  (bit S z src tgt a,state S z w u a)

omit [Fintype V] [Fintype E] in
lemma measurable_snapshot (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) : Measurable (snapshot S z w src tgt u) := by
  exact (Measurable.of_eval (fun e => bit_measurable S z src tgt e)).prodMk
    (Measurable.of_eval (fun x => state_measurable S z w u x))

lemma measurable_value {Y : Type*} [MeasurableSpace Y] (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → Y) :
    Measurable (fun a => F (snapshot S z w src tgt u a)) :=
  (measurable_of_finite F).comp (measurable_snapshot S z w src tgt u)

lemma integrable_value (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → ℝ)
    {ν : Measure (Place K S×ℝ)} [IsFiniteMeasure ν] :
    Integrable (fun a => F (snapshot S z w src tgt u a)) ν := by
  apply Integrable.mono' (integrable_const (∑d : Data V E, |F d|))
    (measurable_value S z w src tgt u F).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a => by
    simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using
      (single_le_sum (s:=univ) (fun d _ => abs_nonneg (F d)) (mem_univ (snapshot S z w src tgt u a)))

lemma integrable_piece (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (F : Data V E → ℝ)
    (v : Place K S) (l r : ℝ) : IntegrableOn (fun s => F (snapshot S z w src tgt u (v,s))) (Icc l r) := by
  apply Integrable.mono' (integrable_const (∑d : Data V E, |F d|))
    ((measurable_value S z w src tgt u F).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa only [Real.norm_eq_abs,Function.comp_apply,id_eq] using
      (single_le_sum (s:=univ) (fun d _ => abs_nonneg (F d)) (mem_univ (snapshot S z w src tgt u (v,s))))

lemma measurable_selection {D : Type*} [MeasurableSpace D] (S : Finset K) (z w : V → K)
    (src tgt : E → V) (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (select : Data V E → D) :
    Measurable (fun a => select (snapshot S z w src tgt u a)) :=
  measurable_value S z w src tgt u select
end
end PlanarUnitDistances.LevelSnapshot

namespace PlanarUnitDistances.ActualSlots
open MeasureTheory Set Finset FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot LevelScores RareScore
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E] [Fintype F]

def frequency (μ : Law E) (a : Data V E) : ℝ := event μ (fun e => a.1 e=true)
def rareException (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x : V) (a : Data V E) : Prop :=
  ¬PlaceScore.common ε (frequency μ a) ∧ good a ∧ exceptional (minority (frequency μ a)) (label a) (a.2 x)
def active (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x : V) (a : Data V E) : ℝ :=
  ind (PlaceScore.common ε (frequency μ a))+ind (rareException ε μ good label x a)

def positive (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (a : Data V E) : ℝ :=
  LevelScores.positive ε (frequency μ a) (event ν (fun j => a.1 (edge j)=true)) (good a)
    (label a) (a.2 x) (a.2 (y e)) (a.2 (y f)) (a.1 (edge e)) (a.1 (edge f))
def score (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (a : Data V E) : ℝ :=
  positive ε μ ν edge y x good label e f a-ind (a.1 (edge e)≠a.1 (edge f))

omit [Fintype V] in
lemma positive_le_active (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (a : Data V E) :
    positive ε μ ν edge y x good label e f a ≤ 2*active ε μ good label x a := by
  by_cases hc : PlaceScore.common ε (frequency μ a)
  · have h := (LevelScores.positive_bounds ε (frequency μ a)
      (event ν (fun j => a.1 (edge j)=true)) (good a) (label a) (a.2 x)
      (a.2 (y e)) (a.2 (y f)) (a.1 (edge e)) (a.1 (edge f))).2
    simpa [positive,active,rareException,hc,ind] using h
  · unfold positive LevelScores.positive active rareException
    rw [ite_eq_right hc]
    by_cases hg : good a
    · rw [ite_eq_left hg]
      by_cases he : exceptional (minority (frequency μ a)) (label a) (a.2 x)
      · simp only [hc,hg,he,true_and,not_false_eq_true,ind,↓reduceIte]
        split_ifs <;> norm_num
      · simp [ind,hc,hg,he]
    · simp [hc,hg,ind]

omit [Fintype V] in
lemma diagonal (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e : F) (a : Data V E) :
    score ε μ ν edge y x good label e e a=positive ε μ ν edge y x good label e e a := by
  simp [score,ind]

lemma measurable_score (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool)) (e f : F) :
    Measurable (fun a => score ε μ ν edge y x good label e f (snapshot S z w src tgt u a)) :=
  measurable_value S z w src tgt u _

lemma score_integrable (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool)) (e f : F) :
    Integrable (fun a => score ε μ ν edge y x good label e f (snapshot S z w src tgt u a))
      (LevelScale.measure S) := integrable_value S z w src tgt u _

lemma negative_integral {l r b c : ℝ} (hlb : l ≤ b) (hbr : b ≤ r) (hlc : l ≤ c) (hcr : c ≤ r) :
    (∫s in Icc l r, ind (decide (s<b)≠decide (s<c)))=|b-c| := by
  have he (s : ℝ) : ind (decide (s<b)≠decide (s<c))=|ThresholdProfiles.bit b s-ThresholdProfiles.bit c s| := by
    by_cases hb : s<b <;> by_cases hc : s<c <;> simp [ind,ThresholdProfiles.bit,hb,hc]
  simp_rw [he]
  exact ThresholdProfiles.bit_sub_integral hlb hbr hlc hcr

lemma integrated_diagonal (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool)) (e : F) :
    (∫a,score ε μ ν edge y x good label e e (snapshot S z w src tgt u a) ∂LevelScale.measure S) ≤
      2*(∫a,active ε μ good label x (snapshot S z w src tgt u a) ∂LevelScale.measure S) := by
  rw [←integral_const_mul]
  apply integral_mono (score_integrable S z w src tgt u ε μ ν edge y x good label e e)
    ((integrable_value S z w src tgt u (active ε μ good label x)).const_mul 2)
  intro a
  dsimp only
  rw [diagonal]
  exact positive_le_active ε μ ν edge y x good label e e _
end
end PlanarUnitDistances.ActualSlots

namespace PlanarUnitDistances.GlobalPairBudget
open MeasureTheory Set Finset Real PlaceLevels BudgetPlaces LevelGeometry PlaceScore
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

lemma total_allowance (S : Finset K) :
    (∑v : Place K S,2*allowance v)/(Module.finrank ℚ K:ℝ)=2*log 2 := by
  rw [Fintype.sum_sum_type]
  simp only [allowance,mul_zero,sum_const_zero,add_zero]
  exact arch_allowance K

lemma thickness_nonneg {S : Finset K} (v : Place K S) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') :
    0 ≤ alpha (av K v) d d'+allowance v := by
  cases v with
  | inl σ => exact alpha_add_log_two_nonneg _ hd hd' hdd
  | inr v =>
    simpa only [av,allowance,add_zero] using alpha_nonneg_nonarch
      (WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2)
      (WeightedAbsoluteValues.finiteEntry_nonarch K v.val.1 v.val.2) hd hd' hdd

lemma cancellation [IsGalois ℚ K] {S : Finset K} {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') (hmem : differenceProduct d d'∈S) :
    (∑v : Place K S,(2*(alpha (av K v) d d'+allowance v)-
      |threshold (av K v) d-threshold (av K v) d'|))/(Module.finrank ℚ K:ℝ)=2*log 2 := by
  have he (v : Place K S) :
      2*(alpha (av K v) d d'+allowance v)-|threshold (av K v) d-threshold (av K v) d'| =
      -log (av K v (differenceProduct d d'))+2*allowance v := by
    rw [place_identity _ hd hd' hdd,max_sub_min_eq_abs,abs_sub_comm (threshold (av K v) d')]
    ring
  simp_rw [he]
  rw [sum_add_distrib,sum_neg_distrib,add_div,neg_div,
    sum_log_product_formula K hmem (differenceProduct_ne_zero hdd),neg_zero,zero_add]
  exact total_allowance S

theorem weighted_pair [IsGalois ℚ K] (S : Finset K) {d d' : K}
    (hd : d≠0) (hd' : d'≠0) (hdd : d≠d') (hmem : differenceProduct d d'∈S)
    {ε : ℝ} (hε : ε<1/2) (g ρ f : Place K S → ℝ → ℝ) (l r : Place K S → ℝ)
    (hg : ∀v,Antitone (g v))
    (hJ : ∀v s,common ε (g v s) ∧ |ρ v s-1/2| ≤ 1/100 ↔ s∈Ico (l v) (r v))
    (hf : ∀v,Integrable (f v))
    (hcap : ∀v s,f v s ≤ cap ε (g v) (ρ v)
      (min (threshold (av K v) d) (threshold (av K v) d'))
      (max (threshold (av K v) d) (threshold (av K v) d'))
      (alpha (av K v) d d'+allowance v) s) :
    (∑v : Place K S,((∫s,f v s)-|threshold (av K v) d-threshold (av K v) d'|)) /
      (Module.finrank ℚ K:ℝ) ≤ 2*log 2+
      (∑v : Place K S,(1/20000:ℝ)*max 0 (r v-l v)*
        (if l v < min (threshold (av K v) d) (threshold (av K v) d') ∧
            min (threshold (av K v) d) (threshold (av K v) d')<r v ∧
            l v < max (threshold (av K v) d) (threshold (av K v) d') ∧
            max (threshold (av K v) d) (threshold (av K v) d')<r v then 1 else 0)) /
      (Module.finrank ℚ K:ℝ) := by
  have hb (v : Place K S) := positive_budget hε (hg v) (min_le_max (a:=threshold (av K v) d)
      (b:=threshold (av K v) d')) (thickness_nonneg v hd hd' hdd) (hJ v) (hf v) (hcap v)
  have hs := sum_le_sum (s:=univ) (fun v _ => sub_le_sub_right (hb v)
    |threshold (av K v) d-threshold (av K v) d'|)
  have he (v : Place K S) (e : ℝ) :
      2*(alpha (av K v) d d'+allowance v)+e-|threshold (av K v) d-threshold (av K v) d'| =
      (2*(alpha (av K v) d d'+allowance v)-|threshold (av K v) d-threshold (av K v) d'|)+e := by ring
  simp_rw [he] at hs
  rw [sum_add_distrib] at hs
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (Module.finrank ℚ K))
  rw [add_div,cancellation hd hd' hdd hmem] at hh
  exact hh
end
end PlanarUnitDistances.GlobalPairBudget

end OAI
