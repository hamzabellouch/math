import OAI.Combinatorics.HadwigerCounterexample.TesterSummaryMass
import OAI.Combinatorics.HadwigerCounterexample.ChannelFrameLaws

namespace OAI

/-! # Ambient Batch Slots -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Function
open scoped BigOperators
variable {I J G A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable {p : Shape} {n N : ℕ}

omit [Fintype B] in
theorem mapW_equiv_val (e : A≃B) (w : Wgt A) (y : B) :
    mapW w e y=w (e.symm y) := by
  classical
  have h : (fun x => e x=y)=(fun x => x=e.symm y) := by
    funext x; apply propext
    exact ⟨fun h => by rw [← h,Equiv.symm_apply_apply],fun h => by rw [h,Equiv.apply_symm_apply]⟩
  unfold mapW; rw [h]; simp

theorem unif_equiv (e : A≃B) : mapW unif e = unif := by
  funext x; rw [mapW_equiv_val, unif_apply, unif_apply, Fintype.card_congr e]

theorem on_equiv (e : A≃B) (p : B→Prop) :
    mapW (unifOn (fun x => p (e x))) e = unifOn p := by
  classical
  have h : nbr (fun x => p (e x))=nbr p := Equiv.sum_comp e (fun y => ind (p y))
  funext x
  rw [mapW_equiv_val,unifOn_val,unifOn_val]; simp only [Equiv.apply_symm_apply,h]

abbrev PlusRack (I : Type) (N : ℕ) := Mat (Fin N) I
abbrev Rack (I : Type) (N : ℕ) := PlusRack I N × PlusRack I N
def sectionR {I J : Type} (f : J→I) (x : Rack I N) : Rack J N :=
  ((x.1).submatrix _root_.id f, (x.2).submatrix _root_.id f)
abbrev Route (I G : Type) := I → G
abbrev Port {I G : Type} (f : Route I G) (g : G) := {i:I//f i=g}
abbrev Network {I G : Type} (f : Route I G) (N : ℕ) := ∀ i,Rack (Port f i) N

variable [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {f : Route I G}

def rackEquiv (f : Route I G) (N : ℕ) : Rack I N ≃ Network f N where
  toFun x i := sectionR Subtype.val x
  invFun x := (Matrix.of (fun j i => (x (f i)).1 j ⟨i,rfl⟩),
    Matrix.of (fun j i => (x (f i)).2 j ⟨i,rfl⟩))
  left_inv x := by apply Prod.ext <;> rfl
  right_inv x := by
    funext i; apply Prod.ext <;>
      · ext j ⟨y,rfl⟩; rfl

abbrev GeoM (f : Route I G) := ∀ i,Mat (Port f i) (Port f i)

def gramPart {N} (A : GeoM f) (x : Rack I N) :=
  ∀ i,let P:=rackEquiv f N x i;
    P.1ᵀ*P.2=A i
def injPart (f : Route I G) {N} (x : Rack I N) :=
  ∀ i,let P:=rackEquiv f N x i;
    Injective P.1.mulVec ∧ Injective P.2.mulVec

def bothPart {N} (A : GeoM f) (x : Rack I N) := ∀ i, gramGood (A i) (rackEquiv f N x i)

def scoreR {I : Type} (x : Rack I N) (i j : I) : F := (x.1ᵀ*x.2) i j

omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
theorem part_scores (x : Rack I N) (A : GeoM f) :
    gramPart A x↔ ∀ i, ∀ a b : Port f i,scoreR x a.val b.val=A i a b := by
  constructor
  · intro h i a b; exact congr_fun (congr_fun (h i) a) b
  intro h i; exact Matrix.ext (fun a b => h i a b)

omit [Fintype G] [DecidableEq I] in
theorem both_test (A : GeoM f) (x : Rack I N) :
    bothPart A x↔ gramPart A x ∧injPart f x := by simp [gramPart,injPart,bothPart,gramGood,forall_and]

private theorem pi_unif {I : Type} [Fintype I] [DecidableEq I]
    {A : I→Type} [∀ i,Fintype (A i)] :
    unif (α:=(∀ i,A i)) = prodW (fun i => unif (α:=A i)) := by
  classical
  funext x
  simp [unif_apply,prodW,Fintype.card_pi]

private theorem pi_unifOn {I : Type} [Fintype I] [DecidableEq I]
    {A : I→Type} [∀ i,Fintype (A i)] (p : ∀ i,A i→Prop) :
    unifOn (fun x => ∀ i,p i (x i)) = prodW (fun i => unifOn (p i)) := by
  classical
  funext x
  rw [unifOn_val]
  have he : nbr (fun x : (∀ i, A i) => ∀ i,p i (x i)) = ∏ i,nbr (p i) := by
    unfold nbr; simp_rw [ind_all]
    exact prodW_tot (fun (i : I) (x : A i) => ind (p i x))
  simp only [prodW,he,unifOn_val,ind_all,Finset.prod_div_distrib]

def rackStation (A : GeoM f) (N : ℕ) : Wgt (Rack I N) := unifOn (bothPart A)
def rackWave (A : GeoM f) (N : ℕ) : Wgt (Rack I N) := unifOn (gramPart A)

theorem station_split (A : GeoM f) (N : ℕ) :
    mapW (rackStation A N) (rackEquiv f N)=
      prodW (fun i => unifOn (gramGood (A i))) := by
  classical
  unfold rackStation bothPart
  rw [show mapW _ _= _ from on_equiv (rackEquiv f N)
    (fun x => ∀ i,gramGood (A i) (x i))]
  exact pi_unifOn _

def netSize (f : Route I G) := ∑ i : G,num (Port f i)*num (Port f i)
def netFact (f : Route I G) :=
  (4:ℝ)^(Fintype.card G)*bp (netSize f)

omit [DecidableEq I] in
theorem netFact_pos : 0<netFact f := mul_pos (pow_pos (by norm_num) _) (bp_pos _)

theorem net_norm (A : GeoM f) (N : ℕ)
    (h : ∀ i,2*num (Port f i)-N≤ -1) :
    (netFact f)⁻¹ ≤ pr unif (bothPart (N:=N) A) ∧
      pr unif (bothPart (N:=N) A) ≤ bp (-netSize f) := by
  classical
  let p := fun i => gramGood (U:=Fin N) (A i)
  have hnum (t : ℕ) : num (Fin t)=(t:ℝ) := by simp [num]
  have ht i : num (Port f i) + num (Port f i)-num (Fin N)≤ -1 := by rw [←two_mul,hnum]; exact h _
  have he : pr unif (bothPart (N:=N) A) = ∏ i,pr unif (p i) := by
    unfold bothPart
    rw [←mapW_pr unif (rackEquiv f N) (fun x => ∀ i,p i (x i)), unif_equiv]
    conv_lhs => rw [pi_unif]
    exact prodW_pr ..
  rw [he]; constructor
  · let h' (i : G) := bp (-(num (Port f i))*num (Port f i))/4
    have hh i : h' i ≤ pr unif (p i) := gram_norm_quarter _ (ht _)
    refine le_trans ?_ (Finset.prod_le_prod₀ (fun i _ => div_nonneg (bp_pos _).le
      (by norm_num)) fun i _ => hh i)
    unfold netFact
    rw [_root_.mul_inv_rev,Finset.prod_div_distrib,←bp_sum,netSize,Finset.prod_const,
      ← bp_neg, ← Finset.sum_neg_distrib]
    simp_rw [neg_mul, Finset.card_univ,div_eq_mul_inv]
    exact le_rfl
  · have h i :=
      (gram_norm (U:=Fin N) (A i) (show _≤ _ by linarith only [ht i])).1
    unfold netSize
    rw [← Finset.sum_neg_distrib, bp_sum]
    apply Finset.prod_le_prod₀ (fun i _ => pr_nonneg unif_law.nz)
    intro i _
    rw [pair_unif,←neg_mul]
    exact h i

theorem wave_norm (A : GeoM f) (N : ℕ)
    (h : ∀ i,2*num (Port f i)-N≤ -1) :
    (netFact f)⁻¹ ≤ pr unif (gramPart (N:=N) A) :=
  ((net_norm A N h).1).trans
    (pr_mono unif_law.nz (fun _ hx => ((both_test ..).mp hx).1))

theorem injPart_failure (f : Route I G) (N : ℕ) (k : ℝ) (h : ∀ i,num (Port f i)≤k) :
    pr unif (fun x : Rack I N => ¬injPart f x)≤num G*(2*bp (k-N)) := by
  classical
  let Q := fun x : Network f N =>
    ∀ i, Injective (x i).1.mulVec ∧ Injective (x i).2.mulVec
  have he :
      pr unif (fun x : Rack I N => ¬injPart f x)=
      pr (prodW (fun i : G => unif (α:=Rack (Port f i) N))) (fun x => ¬Q x) := by
    rw [←pi_unif,← unif_equiv (rackEquiv f N),mapW_pr]
    rfl
  rw [he]
  let P i := fun x : Rack (Port f i) N => ¬ (Injective x.1.mulVec∧Injective x.2.mulVec)
  let w : Wgt (Network f N) := prodW (fun i => unif)
  have hw : IsLaw w := prodW_law (fun _ => unif_law)
  have ht i : pr unif (P i) ≤ 2*bp (k-N) := by
    let g := fun x : PlusRack (Port f i) N => ¬Injective x.mulVec
    have hi : pr unif g≤ bp (k-N) := by
      refine unif_fail.trans (bp_le ?_)
      have he := h i
      simp only [num,Fintype.card_fin] at *
      linarith only [he]
    have hQ (x : Rack (Port f i) N) :
        P i x→ (True∧g x.2)∨(g x.1∧True) := by unfold P g; tauto
    rw [pair_unif,two_mul]
    let nz := (pairW_law (α:=PlusRack (Port f i) N) unif_law (β:=PlusRack (Port f i) N) unif_law).nz
    calc pr _ _
      _ ≤ _ := pr_mono nz hQ
      _ ≤ _ := pr_or_le nz
      _ ≤ _ := by rw [pairW_pr unif unif (fun _ : PlusRack (Port f i) N => True) g,pairW_pr unif unif g (fun _ : PlusRack (Port f i) N => True),pr_true,unif_law.total,one_mul,mul_one]
                  exact add_le_add hi hi
  have hP x (h : ¬Q x) : ∃ i,P i (x i) := Classical.byContradiction (fun g =>
    h (fun i => Classical.byContradiction (fun he => g ⟨i,he⟩)))
  have hc i :
      pr w (fun x => P i (x i))=pr unif (P i) := by
    let g (j : G) (x : Rack (Port f j) N) :=
      if h:j=i then by subst i; exact P j x else True
    have he (x : Network f N) :
        P i (x i) ↔ ∀ j,g j (x j) := by
      constructor
      · intro h j
        by_cases he : j=i
        · subst j; exact (by simpa [g])
        simp [g,he]
      · intro h; simpa [g] using h i
    simp_rw [he]; unfold w; rw [prodW_pr _ g,Finset.prod_eq_single i]
    · simp [g]
    · intro j _ hj; simp [g,hj,unif_law.total]
    simp
  refine le_trans (pr_mono hw.nz hP) ((pr_exists_le hw.nz (fun i x => P i (x i))).trans ?_)
  simp_rw [hc]
  refine (Finset.sum_le_sum fun i _ => ht i).trans_eq ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,num]

end HadwigerCounterexample

end

end OAI
