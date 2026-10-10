import OAI.Geometry.UnitDistances.Tails

namespace OAI

namespace PlanarUnitDistances.PopularCircles
open Finset UnitCodegree
open scoped Classical BigOperators
noncomputable section

def neighbors (S : Finset ℂ) (q : ℂ) : Finset ℂ := S.filter (fun p => dist p q=1)
def candidates (S : Finset ℂ) : Finset ℂ :=
  S.biUnion (fun p => S.biUnion (fun r => if p=r then ∅ else (centerPolynomial p r).roots.toFinset))
def popular (S : Finset ℂ) (k : ℕ) : Finset ℂ :=
  (candidates S).filter (fun q => k≤(neighbors S q).card)
def multiple (S C : Finset ℂ) : Finset ℂ :=
  S.filter (fun p => 2≤(C.filter (fun q => dist p q=1)).card)

lemma mem_neighbors {S : Finset ℂ} {p q : ℂ} : p∈neighbors S q ↔ p∈S ∧ dist p q=1 := mem_filter

lemma mem_candidates {S : Finset ℂ} {q : ℂ} (hq : 2≤(neighbors S q).card) : q∈candidates S := by
  obtain ⟨p,hp,r,hr,hpr⟩ := one_lt_card.mp (by omega : 1<(neighbors S q).card)
  have hp' := mem_neighbors.mp hp
  have hr' := mem_neighbors.mp hr
  apply mem_biUnion.mpr
  refine ⟨p,hp'.1,mem_biUnion.mpr ⟨r,hr'.1,?_⟩⟩
  simp only [hpr,↓reduceIte,Multiset.mem_toFinset]
  exact (Polynomial.mem_roots (centerPolynomial_ne_zero p r hpr)).mpr
    (centerPolynomial_eval p r q (unit_distance_equation p q hp'.2) (unit_distance_equation r q hr'.2))

theorem mem_popular {S : Finset ℂ} {q : ℂ} {k : ℕ} (hk : 2≤k) :
    q∈popular S k ↔ k≤(neighbors S q).card := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    exact mem_filter.mpr ⟨mem_candidates (hk.trans h),h⟩

lemma intersection_card (S : Finset ℂ) {q r : ℂ} (hqr : q≠r) :
    ((neighbors S q).filter (fun p => dist p r=1)).card≤2 := by
  apply unit_centers_card q r hqr
  intro p hp
  have hh := mem_filter.mp hp
  exact ⟨by simpa only [dist_comm] using (mem_neighbors.mp hh.1).2,
    by simpa only [dist_comm] using hh.2⟩

lemma pair_neighbors (S : Finset ℂ) (q : ℂ) :
    S.offDiag.bipartiteAbove (fun (q : ℂ) (pr : ℂ × ℂ) => dist pr.1 q=1 ∧ dist pr.2 q=1) q=
      (neighbors S q).offDiag := by
  ext pr
  simp only [mem_bipartiteAbove,mem_offDiag,mem_neighbors]
  tauto

theorem count (S C : Finset ℂ) {k : ℕ}
    (hk : ∀q∈C,k≤(neighbors S q).card) :
    C.card*(k*(k-1))≤2*S.card^2 := by
  have h := card_nsmul_le_card_nsmul
    (r := fun (q : ℂ) (pr : ℂ × ℂ) => dist pr.1 q=1 ∧ dist pr.2 q=1)
    (s := C) (t := S.offDiag) (m := k*(k-1)) (n := (2:ℕ))
    (fun q hq => by
      rw [pair_neighbors,offDiag_card]
      change k*(k-1)≤(neighbors S q).card*(neighbors S q).card-(neighbors S q).card
      rw [show (neighbors S q).card*(neighbors S q).card-(neighbors S q).card=
        (neighbors S q).card*((neighbors S q).card-1) by rw [Nat.mul_sub_left_distrib,Nat.mul_one]]
      exact Nat.mul_le_mul (hk q hq) (Nat.sub_le_sub_right (hk q hq) 1))
    (fun pr hpr => by
      apply unit_centers_card pr.1 pr.2 (mem_offDiag.mp hpr).2.2
      intro q hq
      exact ((mem_bipartiteBelow _).mp hq).2)
  simp only [nsmul_eq_mul,offDiag_card] at h
  calc
    _ ≤ (S.card*S.card-S.card)*2 := h
    _ ≤ 2*S.card^2 := by nlinarith [Nat.sub_le (S.card*S.card) S.card]

lemma multi_pairs (C : Finset ℂ) (p : ℂ) :
    C.offDiag.bipartiteAbove (fun (p : ℂ) (qr : ℂ × ℂ) => dist p qr.1=1 ∧ dist p qr.2=1) p=
      (C.filter (fun q => dist p q=1)).offDiag := by
  ext qr
  simp only [mem_bipartiteAbove,mem_offDiag,mem_filter]
  tauto

theorem multiple_count (S C : Finset ℂ) : (multiple S C).card≤C.card^2 := by
  have h := card_nsmul_le_card_nsmul
    (r := fun (p : ℂ) (qr : ℂ × ℂ) => dist p qr.1=1 ∧ dist p qr.2=1)
    (s := multiple S C) (t := C.offDiag) (m := 2) (n := (2:ℕ))
    (fun p hp => by
      rw [multi_pairs,offDiag_card]
      have hh := (mem_filter.mp hp).2
      nlinarith [Nat.sub_add_cancel (show (C.filter (fun q => dist p q=1)).card≤
        (C.filter (fun q => dist p q=1)).card*(C.filter (fun q => dist p q=1)).card by nlinarith)])
    (fun qr hqr => by
      apply unit_centers_card qr.1 qr.2 (mem_offDiag.mp hqr).2.2
      intro p hp
      obtain ⟨_,h₁,h₂⟩ := (mem_bipartiteBelow _).mp hp
      exact ⟨by simpa only [dist_comm] using h₁,by simpa only [dist_comm] using h₂⟩)
  simp only [nsmul_eq_mul,offDiag_card] at h
  nlinarith [Nat.sub_le (C.card*C.card) C.card]

theorem exceptional_partner_count (S C : Finset ℂ) {p q : ℂ}
    (hp : p∈S) (hpm : p∉multiple S C) (hq : q∉C) :
    ((neighbors S q).filter (fun r => ∃c∈C,dist p c=1 ∧ dist r c=1)).card≤2 := by
  have hcard : (C.filter (fun c => dist p c=1)).card≤1 := by
    have hh : ¬2≤(C.filter (fun c => dist p c=1)).card := fun h => hpm (mem_filter.mpr ⟨hp,h⟩)
    omega
  by_cases he : ∃c∈C,dist p c=1
  · obtain ⟨c,hc,hpc⟩ := he
    have hu : ∀c'∈C,dist p c'=1 → c'=c := by
      intro c' hc' hpc'
      exact card_le_one.mp hcard c' (mem_filter.mpr ⟨hc',hpc'⟩) c (mem_filter.mpr ⟨hc,hpc⟩)
    have hsub : (neighbors S q).filter (fun r => ∃c∈C,dist p c=1 ∧ dist r c=1) ⊆
        (neighbors S q).filter (fun r => dist r c=1) := by
      intro r hr
      obtain ⟨hr,c',hc',hpc',hrc'⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨hr,by simpa [hu c' hc' hpc'] using hrc'⟩
    exact (card_le_card hsub).trans (intersection_card S (fun h => hq (h ▸ hc)))
  · have hz : (neighbors S q).filter (fun r => ∃c∈C,dist p c=1 ∧ dist r c=1)=∅ := by
      apply filter_eq_empty_iff.mpr
      intro r _ ⟨c,hc,hpc,_⟩
      exact he ⟨c,hc,hpc⟩
    simp only [hz,card_empty]
    omega
end
end PlanarUnitDistances.PopularCircles

namespace PlanarUnitDistances.PopularCircleCost
open Finset FiniteLaw FiniteStarCoupling PopularCircles
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma event_injective_bound {X Y : Type*} [Fintype X] (μ : Law X) (f : X → Y)
    (hf : Function.Injective f) (S : Finset Y) {d : ℝ} (hd : 0 ≤ d)
    (hμ : ∀x,μ.val x ≤ d) : event μ (fun x => f x∈S) ≤ (S.card:ℝ)*d := by
  classical
  let A := univ.filter (fun x => f x∈S)
  have hcard : A.card ≤ S.card := by
    rw [←card_image_of_injective A hf]
    exact card_le_card (by intro y hy; obtain ⟨x,hx,rfl⟩ := mem_image.mp hy; exact (mem_filter.mp hx).2)
  calc
    _ = ∑x∈A,μ.val x := by
      simp only [A,sum_filter,event_eq_sum]
      apply sum_congr rfl
      intro x _
      split_ifs <;> rfl
    _ ≤ ∑x∈A,d := by apply sum_le_sum; exact fun x _ => hμ x
    _ = (A.card:ℝ)*d := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hd

lemma support_event_bound {X Y : Type*} [Fintype X] (μ : Law X) (f : X → Y)
    (hf : Function.Injective f) (S : Finset Y) (A : X → Prop)
    {d : ℝ} (hd : 0 ≤ d) (hμ : ∀x,μ.val x ≤ d)
    (hs : ∀x,0<μ.val x → A x → f x∈S) : event μ A ≤ (S.card:ℝ)*d := by
  have h : event μ A=event μ (fun x => A x ∧ f x∈S) := by
    unfold event avg
    apply sum_congr rfl
    intro x _
    by_cases hx : 0<μ.val x
    · by_cases ha : A x
      · simp [ha,hs x hx ha]
      · simp [ha]
    · have hz := le_antisymm (le_of_not_gt hx) (μ.nonneg x)
      simp [hz]
  rw [h]
  exact (event_mono μ (fun _ h => h.2)).trans (event_injective_bound μ f hf S hd hμ)

theorem cost (π : Law (P×Q)) (x : P → ℂ) (y : Q → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (S C : Finset ℂ) (hS : ∀p,x p∈S)
    (hu : ∀q p,0<(col π q).val p → dist (x p) (y q)=1)
    {μmax κmax d : ℝ} (hμ0 : 0 ≤ μmax) (hκ0 : 0 ≤ κmax) (hd0 : 0 ≤ d)
    (hμ : ∀p,(left π).val p ≤ μmax) (hκ : ∀q,(right π).val q ≤ κmax)
    (hd : ∀q p,(col π q).val p ≤ d) :
    event (WedgeLaw.law π) (fun a => ∃c∈C,dist (x a.2.1) c=1 ∧ dist (x a.2.2) c=1) ≤
      2*(C.card:ℝ)^2*μmax+(C.card:ℝ)*κmax+2*d := by
  let bad : P → P → Prop := fun p r => ∃c∈C,dist (x p) c=1 ∧ dist (x r) c=1
  let mult : P → Prop := fun p => x p∈multiple S C
  let cent : Q → Prop := fun q => y q∈C
  let residual : Q×(P×P) → Prop := fun a => ¬mult a.2.1 ∧ ¬cent a.1 ∧ bad a.2.1 a.2.2
  have hfirst : event (WedgeLaw.law π) (fun a => mult a.2.1) ≤ (C.card:ℝ)^2*μmax := by
    have he : event (WedgeLaw.law π) (fun a => mult a.2.1)=event (left π) mult :=
      by
        rw [←avg_ite (WedgeLaw.law π) (fun a => mult a.2.1),←avg_ite (left π) mult]
        exact WedgeLaw.first_point π (fun p => if mult p then 1 else 0)
    rw [he]
    calc
      _ ≤ ((multiple S C).card:ℝ)*μmax := event_injective_bound (left π) x hx _ hμ0 hμ
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast multiple_count S C) hμ0
  have hcenter : event (WedgeLaw.law π) (fun a => cent a.1) ≤ (C.card:ℝ)*κmax := by
    have he : event (WedgeLaw.law π) (fun a => cent a.1)=event (right π) cent := by
      unfold event
      rw [WedgeLaw.average]
      apply congrArg (avg (right π))
      funext q
      by_cases hc : cent q
      · simp only [hc,↓reduceIte,avg_const]
      · simp only [hc,↓reduceIte,avg_const]
    rw [he]
    exact event_injective_bound (right π) y hy C hκ0 hκ
  have hres : event (WedgeLaw.law π) residual ≤ 2*d := by
    unfold event
    rw [WedgeLaw.average]
    calc
      _ ≤ avg (right π) (fun _ => 2*d) := by
        apply avg_mono
        intro q
        rw [pair_avg]
        calc
          _ ≤ avg (col π q) (fun _ => 2*d) := by
            apply avg_mono
            intro p
            by_cases hp : mult p
            · simp only [residual,hp,not_true_eq_false,false_and,↓reduceIte,avg_const]
              positivity
            by_cases hq : cent q
            · simp only [residual,hq,not_true_eq_false,and_false,false_and,↓reduceIte,avg_const]
              positivity
            simp only [residual,hp,hq,not_false_eq_true,true_and]
            rw [avg_ite]
            let B := (neighbors S (y q)).filter (fun r => ∃c∈C,dist (x p) c=1 ∧ dist r c=1)
            have hc : B.card ≤ 2 := exceptional_partner_count S C (hS p) hp hq
            calc
              _ ≤ (B.card:ℝ)*d := support_event_bound (col π q) x hx B (bad p) hd0 (hd q)
                (fun r hr hbr => mem_filter.mpr ⟨mem_neighbors.mpr ⟨hS r,hu q r hr⟩,hbr⟩)
              _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) hd0
          _ = _ := avg_const _ _
      _ = _ := avg_const _ _
  have hcover : event (WedgeLaw.law π) (fun a => bad a.2.1 a.2.2) ≤
      event (WedgeLaw.law π) (fun a => mult a.2.1)+
      event (WedgeLaw.law π) (fun a => cent a.1)+event (WedgeLaw.law π) residual := by
    calc
      _ ≤ event (WedgeLaw.law π) (fun a => (mult a.2.1 ∨ cent a.1) ∨ residual a) := by
        apply event_mono
        intro a ha
        by_cases hp : mult a.2.1
        · exact Or.inl (Or.inl hp)
        by_cases hq : cent a.1
        · exact Or.inl (Or.inr hq)
        exact Or.inr ⟨hp,hq,ha⟩
      _ ≤ _ := (event_union_le _ _ _).trans (add_le_add (event_union_le _ _ _) le_rfl)
  have hn : 0 ≤ (C.card:ℝ)^2*μmax := by positivity
  change event (WedgeLaw.law π) (fun a => bad a.2.1 a.2.2) ≤ _
  linarith
end
end PlanarUnitDistances.PopularCircleCost

namespace PlanarUnitDistances.IncidencePopular
open Filter Finset FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale PowerGrowth
open scoped Classical
noncomputable section
variable (s : Sequence)
def points (i : ℕ) : Finset ℂ := (s.P i).image UnitCodegree.zCoordinate
def k (i : ℕ) : ℕ := ⌈s.t i^(9/10:ℝ)⌉₊
def centers (i : ℕ) : Finset ℂ := PopularCircles.popular (points s i) (k s i)
def bad (i : ℕ) (a : s.Q i×(s.P i×s.P i)) : Prop :=
  ∃c∈centers s i,dist (UnitCodegree.zCoordinate a.2.1.val) c=1 ∧
    dist (UnitCodegree.zCoordinate a.2.2.val) c=1
lemma points_card (i : ℕ) : (points s i).card=(s.P i).card :=
  card_image_of_injective _ UnitCodegree.zCoordinate.injective
lemma tpos (i : ℕ) : 0<s.t i := by linarith [s.large i,Nat.cast_nonneg (α:=ℝ) i]
lemma center_atom (i : ℕ) (q : s.Q i) :
    (right (graph s i)).val q ≤ s.t i^(-1/2:ℝ) := by
  have hp : 0<((s.P i).card:ℝ) := Nat.cast_pos.mpr (GeometricLaw.card_pos _ _ (s.good i).positive).1
  have he := (s.good i).positive
  have hdp := (s.good i).degreeP
  have hm := (le_div_iff₀ hp).mp hdp
  have hpow := Real.rpow_pos_of_pos (tpos s i) (1/2:ℝ)
  rw [graph,GeometricLaw.right_eq]
  calc
    _ ≤ ((s.P i).card:ℝ)/CircleIncidence.incidences (s.P i) (s.Q i) :=
      div_le_div_of_nonneg_right (show CircleIncidence.degree (s.P i) q ≤ ((s.P i).card:ℝ) from by
        unfold CircleIncidence.degree
        exact_mod_cast Finset.card_filter_le (s.P i) _) he.le
    _ ≤ (27/50:ℝ)/(s.t i^(1/2:ℝ)) := by
      apply (div_le_div_iff₀ he hpow).mpr
      nlinarith
    _ ≤ 1/(s.t i^(1/2:ℝ)) := div_le_div_of_nonneg_right (by norm_num) hpow.le
    _ = s.t i^(-1/2:ℝ) := by rw [one_div,←Real.rpow_neg (tpos s i).le]; congr 1; norm_num
lemma column_atom (i : ℕ) (q : s.Q i) (p : s.P i) :
    (col (graph s i) q).val p ≤ 1/((i:ℝ)+1) := by
  have hp := (s.good i).center_degree_pos q
  have he := (s.good i).positive
  have hb := (le_div_iff₀ he).mp ((s.good i).atomQ q q.property)
  have hd : (i:ℝ)+1 ≤ CircleIncidence.degree (s.P i) q :=
    (s.good i).degreeQ.trans (by simpa only [div_mul_eq_mul_div] using hb)
  rw [graph,GeometricLaw.graph,UniformGraphLaw.col_eq _ _ (by rw [GeometricLaw.degree_eq]; exact hp),GeometricLaw.degree_eq]
  apply le_trans (div_le_div_of_nonneg_right (b:=(1:ℝ)) ?_ hp.le)
  · exact one_div_le_one_div_of_le (by positivity) hd
  · unfold IncidenceEntropy.indicator
    split_ifs <;> norm_num
lemma k_large : ∀ᶠi in atTop,2≤k s i := by
  filter_upwards [((tendsto_rpow_atTop (by norm_num : (0:ℝ)<9/10)).comp s.tendsto).eventually_ge_atTop 2] with i hi
  have hh := hi.trans (Nat.le_ceil (s.t i^(9/10:ℝ)))
  exact_mod_cast hh
lemma count_bound : ∀ᶠi in atTop,(centers s i).card≤ s.t i^(6/25:ℝ) := by
  have hc := s.cardP_power.power_bound (by norm_num : (1:ℝ)<101/100)
  have hfort := eventually_constant_le_rpow s.tendsto (by norm_num : (0:ℝ)<1/50) 4
  filter_upwards [k_large s,hc,hfort] with i hk hc hfort
  have hcount := PopularCircles.count (points s i) (centers s i)
    (fun q hq => (PopularCircles.mem_popular hk).mp hq)
  have hk1 : 1≤k s i := by omega
  have hkr : (2:ℝ)≤k s i := by exact_mod_cast hk
  have hh : (centers s i).card*((k s i:ℝ)*((k s i:ℝ)-1))≤2*((s.P i).card:ℝ)^2 := by
    rw [points_card] at hcount
    exact_mod_cast hcount
  have hk0 := Nat.le_ceil (s.t i^(9/10:ℝ))
  have hpos := Real.rpow_pos_of_pos (tpos s i) (9/10:ℝ)
  have hcc : 0≤((centers s i).card:ℝ) := Nat.cast_nonneg _
  have hsquare : (s.t i^(9/10:ℝ))^2≤(k s i:ℝ)^2  := by gcongr; exact hk0
  have hc' : ((s.P i).card:ℝ)^2≤(s.t i^(101/100:ℝ))^2 := by gcongr
  have hbound : ((centers s i).card:ℝ)*(s.t i^(9/10:ℝ))^2 ≤ 4*(s.t i^(101/100:ℝ))^2 := by
    have hm := mul_le_mul_of_nonneg_left hsquare hcc
    nlinarith [mul_nonneg hcc (show 0≤(k s i:ℝ)*((k s i:ℝ)-2) by positivity)]
  have hp2 : (s.t i^(9/10:ℝ))^2=s.t i^(9/5:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul (tpos s i).le]; norm_num
  have hp3 : (s.t i^(101/100:ℝ))^2=s.t i^(101/50:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul (tpos s i).le]; norm_num
  rw [hp2,hp3] at hbound
  have hb : ((centers s i).card:ℝ)≤4*s.t i^(11/50:ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos (tpos s i) (9/5:ℝ))).mp
    calc
      _ ≤ 4*s.t i^(101/50:ℝ) := hbound
      _ = _ := by rw [mul_assoc,←Real.rpow_add (tpos s i)]; norm_num
  calc
    _ ≤ 4*s.t i^(11/50:ℝ) := hb
    _ ≤ s.t i^(1/50:ℝ)*s.t i^(11/50:ℝ) := mul_le_mul_of_nonneg_right hfort (Real.rpow_nonneg (tpos s i).le _)
    _ = _ := by rw [←Real.rpow_add (tpos s i)]; norm_num
lemma cost (i : ℕ) : event (WedgeLaw.law (graph s i)) (bad s i)≤
    2*((centers s i).card:ℝ)^2*s.t i^(-1/2:ℝ)+((centers s i).card:ℝ)*s.t i^(-1/2:ℝ)+2/((i:ℝ)+1) := by
  apply (PopularCircleCost.cost (graph s i) (fun p => UnitCodegree.zCoordinate p.val)
    (fun q => UnitCodegree.zCoordinate q.val)
    (UnitCodegree.zCoordinate.injective.comp Subtype.val_injective)
    (UnitCodegree.zCoordinate.injective.comp Subtype.val_injective)
    (points s i) (centers s i) (fun p => mem_image.mpr ⟨p.val,p.property,rfl⟩)
    (fun q p h => ?_) (Real.rpow_nonneg (tpos s i).le _) (Real.rpow_nonneg (tpos s i).le _)
    (by positivity) (point_bound s i) (center_atom s i) (column_atom s i)).trans_eq
  · ring
  · rw [UnitCodegree.zCoordinate.dist_map]
    have hπ : 0<(graph s i).val (p,q) := by
      rw [←col_weight]
      exact mul_pos (positiveQ s i q) h
    exact IncidenceScale.support s i p q hπ
lemma cost_limit : Tendsto (fun i => event (WedgeLaw.law (graph s i)) (bad s i)) atTop (nhds 0) := by
  have h₁ : Tendsto (fun i => s.t i^(-1/50:ℝ)) atTop (nhds 0) :=
    by simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/50)).comp s.tendsto
  have h₂ : Tendsto (fun i => s.t i^(-13/50:ℝ)) atTop (nhds 0) :=
    by simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<13/50)).comp s.tendsto
  have hlim : Tendsto (fun i => 2*s.t i^(-1/50:ℝ)+s.t i^(-13/50:ℝ)+2/((i:ℝ)+1)) atTop (nhds 0) := by
    convert ((h₁.const_mul 2).add h₂).add (Sequence.accuracy_limit.const_mul 2) using 1 <;> simp [div_eq_mul_inv]
  apply squeeze_zero' (Eventually.of_forall (fun i => event_nonneg _ _)) _ hlim
  filter_upwards [count_bound s] with i hi
  calc
    _ ≤ _ := cost s i
    _ ≤ 2*(s.t i^(6/25:ℝ))^2*s.t i^(-1/2:ℝ)+s.t i^(6/25:ℝ)*s.t i^(-1/2:ℝ)+2/((i:ℝ)+1) := by
      have ht := tpos s i
      gcongr
    _ = _ := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (tpos s i).le,mul_assoc,←Real.rpow_add (tpos s i),←Real.rpow_add (tpos s i)]
      norm_num
end
end PlanarUnitDistances.IncidencePopular

namespace PlanarUnitDistances.LawDeletion
open FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {X P Q : Type*} [Fintype X] [Fintype P] [Fintype Q]
def keep (μ : Law X) (A B : X → Prop) (x : X) : Prop := 0<μ.val x ∧ A x ∧ ¬B x
lemma cost (μ : Law X) (A B : X → Prop) :
    event μ A≤event μ (keep μ A B)+event μ B := by
  unfold event
  rw [←avg_add]
  apply FiniteLawIntegral.avg_mono_support
  intro x hx
  by_cases ha : A x <;> by_cases hb : B x <;> simp [keep,hx,ha,hb]
lemma wedge_support (π : Law (P×Q)) (a : Q×(P×P)) (ha : 0<(WedgeLaw.law π).val a) :
    0<π.val (a.2.1,a.1) ∧ 0<π.val (a.2.2,a.1) := by
  change 0<(right π).val a.1*((col π a.1).val a.2.1*(col π a.1).val a.2.2) at ha
  have hq : 0<(right π).val a.1 := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) ((right π).nonneg a.1)
    simp [hz] at ha
  have hpair := (mul_pos_iff_of_pos_left hq).mp ha
  have hp : 0<(col π a.1).val a.2.1 := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) ((col π a.1).nonneg a.2.1)
    simp [hz] at hpair
  have hr : 0<(col π a.1).val a.2.2 := (mul_pos_iff_of_pos_left hp).mp hpair
  constructor <;> rw [←col_weight]
  · exact mul_pos hq hp
  · exact mul_pos hq hr
end
end PlanarUnitDistances.LawDeletion

namespace PlanarUnitDistances.PlaceLogGeometry
open Finset PlaceLevels WeightedAbsoluteValues
open scoped BigOperators Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

def supported (S : Finset K) (x : K) : Prop :=
  ∀v : Nat.Primes×Gal(K/ℚ),v∉finiteSupport K S → Real.log (finiteEntry K v.1 v.2 x)=0

lemma supported_of_mem {S : Finset K} {x : K} (hx : x∈S) : supported S x :=
  fun _ hv => log_off_support K hx hv

omit [NumberField K] in
lemma log_mul (v : AbsoluteValue K ℝ) {x y : K} (hx : x≠0) (hy : y≠0) :
    Real.log (v (x*y))=Real.log (v x)+Real.log (v y) := by
  rw [map_mul,Real.log_mul (v.pos hx).ne' (v.pos hy).ne']
omit [NumberField K] in
lemma log_div (v : AbsoluteValue K ℝ) {x y : K} (hx : x≠0) (hy : y≠0) :
    Real.log (v (x/y))=Real.log (v x)-Real.log (v y) := by
  rw [map_div₀,Real.log_div (v.pos hx).ne' (v.pos hy).ne']
lemma supported_mul {S : Finset K} {x y : K} (hx : x≠0) (hy : y≠0)
    (hsx : supported S x) (hsy : supported S y) : supported S (x*y) := by
  intro v hv
  rw [log_mul _ hx hy,hsx v hv,hsy v hv,add_zero]
lemma supported_div {S : Finset K} {x y : K} (hx : x≠0) (hy : y≠0)
    (hsx : supported S x) (hsy : supported S y) : supported S (x/y) := by
  intro v hv
  rw [log_div _ hx hy,hsx v hv,hsy v hv,sub_self]

lemma height_identity [IsGalois ℚ K] (S : Finset K) {x : K} (hx : x≠0) (hs : supported S x) :
    (LevelScale.weight K:ℝ)*(∑v : Place K S,|Real.log (av K v x)|)=2*exactHeight K x := by
  have hf : (∑v : ↥(finiteSupport K S),|Real.log (finiteEntry K v.val.1 v.val.2 x)|)=
      ∑ᶠv : Nat.Primes×Gal(K/ℚ),|Real.log (finiteEntry K v.1 v.2 x)| := by
    rw [Finset.sum_coe_sort (finiteSupport K S) (fun v => |Real.log (finiteEntry K v.1 v.2 x)|)]
    symm
    apply finsum_eq_sum_of_support_subset
    intro v hv
    by_contra hn
    apply hv
    simp only [hs v hn,abs_zero]
  rw [Fintype.sum_sum_type]
  change (Module.finrank ℚ K:ℝ)⁻¹*((∑σ : K →ₐ[ℚ] ℂ,|Real.log (infiniteEntry K σ x)|)+
    (∑v : ↥(finiteSupport K S),|Real.log (finiteEntry K v.val.1 v.val.2 x)|))=_
  rw [hf,mul_comm,←div_eq_mul_inv]
  exact weighted_abs_log_eq_twice K hx

omit [NumberField K] in
lemma unit_pair_identity {d d' e e' : K} (hd : d≠0) (hd' : d'≠0)
    (he : d*e=1) (he' : d'*e'=1) :
    (d-d')*(e-e')=2-d/d'-(d/d')⁻¹ := by
  have h₁ : e=1/d := (eq_div_iff hd).mpr (by simpa only [mul_comm] using he)
  have h₂ : e'=1/d' := (eq_div_iff hd').mpr (by simpa only [mul_comm] using he')
  rw [h₁,h₂]
  field_simp
  ring

theorem rectangle [IsGalois ℚ K] (S : Finset K) (a b c d : K)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0)
    (hsa : supported S a) (hsb : supported S b) (hsc : supported S c) (hsd : supported S d)
    (f f' g g' : Place K S → ℝ) {E₁ E₂ E₃ E₄ : ℝ}
    (h₁ : (LevelScale.weight K:ℝ)*(∑v,|Real.log (av K v a)+f v-g v|)≤E₁)
    (h₂ : (LevelScale.weight K:ℝ)*(∑v,|Real.log (av K v b)+f' v-g' v|)≤E₂)
    (h₃ : (LevelScale.weight K:ℝ)*(∑v,|Real.log (av K v c)+f v-g' v|)≤E₃)
    (h₄ : (LevelScale.weight K:ℝ)*(∑v,|Real.log (av K v d)+f' v-g v|)≤E₄) :
    2*exactHeight K (a*b/(c*d))≤E₁+E₂+E₃+E₄ := by
  have hx := div_ne_zero (mul_ne_zero ha hb) (mul_ne_zero hc hd)
  have hs := supported_div (mul_ne_zero ha hb) (mul_ne_zero hc hd)
    (supported_mul ha hb hsa hsb) (supported_mul hc hd hsc hsd)
  rw [←height_identity S hx hs]
  have hh : ∀v : Place K S,|Real.log (av K v (a*b/(c*d)))|≤
      |Real.log (av K v a)+f v-g v|+|Real.log (av K v b)+f' v-g' v|+
      |Real.log (av K v c)+f v-g' v|+|Real.log (av K v d)+f' v-g v| := by
    intro v
    rw [log_div _ (mul_ne_zero ha hb) (mul_ne_zero hc hd),log_mul _ ha hb,log_mul _ hc hd]
    have he : Real.log (av K v a)+Real.log (av K v b)-(Real.log (av K v c)+Real.log (av K v d))=
        (Real.log (av K v a)+f v-g v)+(Real.log (av K v b)+f' v-g' v)-
        (Real.log (av K v c)+f v-g' v)-(Real.log (av K v d)+f' v-g v) := by ring
    rw [he]
    have h₁ := abs_sub
      ((Real.log (av K v a)+f v-g v)+(Real.log (av K v b)+f' v-g' v)-(Real.log (av K v c)+f v-g' v))
      (Real.log (av K v d)+f' v-g v)
    have h₂ := abs_sub
      ((Real.log (av K v a)+f v-g v)+(Real.log (av K v b)+f' v-g' v))
      (Real.log (av K v c)+f v-g' v)
    have h₃ := abs_add_le (Real.log (av K v a)+f v-g v) (Real.log (av K v b)+f' v-g' v)
    linarith

  have h := mul_le_mul_of_nonneg_left (sum_le_sum (s := univ) (fun v _ => hh v))
    (NNReal.coe_nonneg (LevelScale.weight K))
  simp only [sum_add_distrib,mul_add] at h
  linarith
end
end PlanarUnitDistances.PlaceLogGeometry

end OAI
