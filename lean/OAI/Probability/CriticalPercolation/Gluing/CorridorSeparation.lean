import Mathlib

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.Corridor

abbrev Site := ℤ×ℤ
abbrev Point := ℝ×ℝ
abbrev Edge := Site×Bool

def source (e : Edge) : Site := e.1
def target (e : Edge) : Site := if e.2 then e.1+(1,0) else e.1+(0,1)
def endpoints (e : Edge) : Set Site := {source e,target e}

def box (j h : ℝ) (v : Site) : Set Point := {x |
    |x.1-((v.1 : ℝ)+v.2)|≤j ∧ |x.2-((v.1 : ℝ)-v.2)|≤j+h}

def tube (h : ℝ) (e : Edge) : Set Point := {x |
    (e.1.1 : ℝ)+e.1.2≤x.1 ∧ x.1≤(e.1.1 : ℝ)+e.1.2+1 ∧
    if e.2 then |x.2-(x.1-2*(e.1.2 : ℝ))|≤h
    else |x.2-(2*(e.1.1 : ℝ)-x.1)|≤h}

def domain (j h : ℝ) (e : Edge) : Set Point :=
  box j h (source e)∪box j h (target e)∪tube h e

lemma int_eq_of_close (a b : ℤ) (h1 : (a : ℝ)-b<1) (h2 : (b : ℝ)-a<1) : a=b := by
  have h1' : a-b<1 := by exact_mod_cast h1
  have h2' : b-a<1 := by exact_mod_cast h2
  omega

lemma int_endpoint_interval (a b : ℤ) (h1 : (a : ℝ)-b<1) (h2 : (b : ℝ)-a<2) :
    b=a ∨ b=a+1 := by
  have h1' : a-b<1 := by exact_mod_cast h1
  have h2' : b-a<2 := by exact_mod_cast h2
  omega

lemma box_disjoint (j h : ℝ) (hs : 2*j+h<1) {v w : Site} (hv : v≠w) :
    Disjoint (box j h v) (box j h w) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hx1,hx2⟩ := hx
  obtain ⟨hy1,hy2⟩ := hy
  rw [abs_le] at hx1 hx2 hy1 hy2
  apply hv
  apply Prod.ext
  · apply int_eq_of_close <;> linarith
  · apply int_eq_of_close <;> linarith

lemma box_tube_endpoint (j h : ℝ) (hs : j+h<1) (hj : j<1)
    {v : Site} {e : Edge} {x : Point} (hx : x∈box j h v) (hy : x∈tube h e) :
    v=source e ∨ v=target e := by
  obtain ⟨a,b⟩ := v
  obtain ⟨⟨c,d⟩,s⟩ := e
  obtain ⟨hx1,hx2⟩ := hx
  rw [abs_le] at hx1 hx2
  cases s with
  | true =>
    change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(x.1-2*(d : ℝ))|≤h at hy
    rw [abs_le] at hy
    have hb : b=d := int_eq_of_close _ _ (by linarith) (by linarith)
    subst d
    have ha : a=c ∨ a=c+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
    rcases ha with rfl|rfl <;> simp [source,target]
  | false =>
    change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
    rw [abs_le] at hy
    have ha : a=c := int_eq_of_close _ _ (by linarith) (by linarith)
    subst c
    have hb : b=d ∨ b=d+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
    rcases hb with rfl|rfl <;> simp [source,target]

lemma tubes_opposite (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) {x : Point} (hx : x∈tube h ((a,b),true))
    (hy : x∈tube h ((c,d),false)) :
    ∃ v, v∈endpoints ((a,b),true) ∧ v∈endpoints ((c,d),false) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(x.1-2*(b : ℝ))|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
  rw [abs_le] at hx hy
  have hac : c=a ∨ c=a+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
  have hdb : b=d ∨ b=d+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
  refine ⟨(c,b),?_,?_,?_⟩
  · rcases hac with rfl|rfl <;> simp [endpoints,source,target]
  · rcases hdb with rfl|rfl <;> simp [endpoints,source,target]
  · constructor <;> rw [abs_le] <;> constructor <;> dsimp <;> linarith

lemma tubes_parallel_true (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) (hne : (a,b)≠(c,d)) {x : Point}
    (hx : x∈tube h ((a,b),true)) (hy : x∈tube h ((c,d),true)) :
    ∃ v, v∈endpoints ((a,b),true) ∧ v∈endpoints ((c,d),true) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(x.1-2*(b : ℝ))|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(x.1-2*(d : ℝ))|≤h at hy
  rw [abs_le] at hx hy
  have hb : b=d := int_eq_of_close _ _ (by linarith) (by linarith)
  subst d
  have ha : a≠c := by intro h; subst c; exact hne rfl
  have hab : a=c+1 ∨ c=a+1 := by
    have h1 : a≤c+1 := by exact_mod_cast (show (a : ℝ)≤c+1 by linarith)
    have h2 : c≤a+1 := by exact_mod_cast (show (c : ℝ)≤a+1 by linarith)
    omega
  rcases hab with rfl|rfl
  · refine ⟨(c+1,b),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
  · refine ⟨(a+1,b),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith

lemma tubes_parallel_false (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) (hne : (a,b)≠(c,d)) {x : Point}
    (hx : x∈tube h ((a,b),false)) (hy : x∈tube h ((c,d),false)) :
    ∃ v, v∈endpoints ((a,b),false) ∧ v∈endpoints ((c,d),false) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(2*(a : ℝ)-x.1)|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
  rw [abs_le] at hx hy
  have ha : a=c := int_eq_of_close _ _ (by linarith) (by linarith)
  subst c
  have hb : b≠d := by intro h; subst d; exact hne rfl
  have hbd : b=d+1 ∨ d=b+1 := by
    have h1 : b≤d+1 := by exact_mod_cast (show (b : ℝ)≤d+1 by linarith)
    have h2 : d≤b+1 := by exact_mod_cast (show (d : ℝ)≤b+1 by linarith)
    omega
  rcases hbd with rfl|rfl
  · refine ⟨(a,d+1),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
  · refine ⟨(a,b+1),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith

lemma distinct_tubes_intersection (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    {e f : Edge} (hne : e≠f) {x : Point} (hx : x∈tube h e) (hy : x∈tube h f) :
    ∃ v, v∈endpoints e ∧ v∈endpoints f ∧ x∈box j h v := by
  obtain ⟨⟨a,b⟩,s⟩ := e
  obtain ⟨⟨c,d⟩,t⟩ := f
  cases s <;> cases t
  · exact tubes_parallel_false j h hh hhj hh1 a b c d (by intro he; exact hne (congrArg (fun z => (z,false)) he)) hx hy
  · obtain ⟨v,hv,hv',hb⟩ := tubes_opposite j h hh hhj hh1 c d a b hy hx
    exact ⟨v,hv',hv,hb⟩
  · exact tubes_opposite j h hh hhj hh1 a b c d hx hy
  · exact tubes_parallel_true j h hh hhj hh1 a b c d (by intro he; exact hne (congrArg (fun z => (z,true)) he)) hx hy

lemma box_domain_endpoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {v : Site} {e : Edge} {x : Point} (hx : x∈box j h v) (hy : x∈domain j h e) :
    v∈endpoints e := by
  rcases hy with (hy|hy)|hy
  · have he : v=source e := by
      by_contra he
      exact Set.disjoint_left.mp (box_disjoint j h hs he) hx hy
    simp [endpoints,he]
  · have he : v=target e := by
      by_contra he
      exact Set.disjoint_left.mp (box_disjoint j h hs he) hx hy
    simp [endpoints,he]
  · exact (box_tube_endpoint j h (by linarith) (by linarith) hx hy)

theorem distinct_domains_intersection (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hne : e≠f) {x : Point} (hx : x∈domain j h e) (hy : x∈domain j h f) :
    ∃ v, v∈endpoints e ∧ v∈endpoints f ∧ x∈box j h v := by
  rcases hx with (hx|hx)|hx
  · exact ⟨source e,by simp [endpoints],box_domain_endpoint j h hh hhj hs hx hy,hx⟩
  · exact ⟨target e,by simp [endpoints],box_domain_endpoint j h hh hhj hs hx hy,hx⟩
  · rcases hy with (hy|hy)|hy
    · exact ⟨source f,box_domain_endpoint j h hh hhj hs hy (Or.inr hx),by simp [endpoints],hy⟩
    · exact ⟨target f,box_domain_endpoint j h hh hhj hs hy (Or.inr hx),by simp [endpoints],hy⟩
    · exact distinct_tubes_intersection j h hh hhj (by linarith) hne hx hy

lemma common_endpoint_unique {e f : Edge} (hne : e≠f) {v w : Site}
    (hve : v∈endpoints e) (hvf : v∈endpoints f)
    (hwe : w∈endpoints e) (hwf : w∈endpoints f) : v=w := by
  obtain ⟨⟨a,b⟩,s⟩ := e
  obtain ⟨⟨c,d⟩,t⟩ := f
  obtain ⟨u,v⟩ := v
  obtain ⟨x,y⟩ := w
  cases s <;> cases t <;>
    simp [endpoints,source,target,Prod.ext_iff] at * <;> omega

lemma incident_domains_intersection (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hne : e≠f) {v : Site} (he : v∈endpoints e) (hf : v∈endpoints f) :
    domain j h e∩domain j h f⊆box j h v := by
  intro x hx
  obtain ⟨w,hwe,hwf,hw⟩ := distinct_domains_intersection j h hh hhj hs hne hx.1 hx.2
  have h := common_endpoint_unique hne hwe hwf he hf
  rwa [h] at hw

lemma nonincident_domains_disjoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (he : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (domain j h e) (domain j h f) := by
  have hne : e≠f := by
    intro hh
    subst f
    exact Set.disjoint_left.mp he (show source e∈endpoints e by simp [endpoints])
      (by simp [endpoints])
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨v,hv,hv',_⟩ := distinct_domains_intersection j h hh hhj hs hne hx hy
  exact Set.disjoint_left.mp he hv hv'

lemma nonendpoint_domain_box_disjoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e : Edge} {v : Site} (hv : v∉endpoints e) : Disjoint (box j h v) (domain j h e) := by
  exact Set.disjoint_left.mpr fun _ hx hy => hv (box_domain_endpoint j h hh hhj hs hx hy)

lemma source_scales (J L : ℝ) (hJ : 26200<J) (hL : 10*(J+210)<L) :
    0≤630/((1/4:ℝ)*(L+1/2)) ∧
    630/((1/4:ℝ)*(L+1/2))≤J/(L+1/2) ∧
    2*(J/(L+1/2))+630/((1/4:ℝ)*(L+1/2))<1 := by
  have hT : 0<L+1/2 := by linarith
  have he : 630/((1/4:ℝ)*(L+1/2))=2520/(L+1/2) := by field_simp; ring
  rw [he]
  refine ⟨(div_nonneg (by norm_num) hT.le),?_,?_⟩
  · exact (div_le_div_iff_of_pos_right hT).mpr (by linarith)
  · have h1 : 2*(J/(L+1/2))+2520/(L+1/2)=(2*J+2520)/(L+1/2) := by ring
    rw [h1]
    exact (div_lt_one hT).mpr (by linarith)

end CriticalPercolation.Corridor
end
end
end

end OAI
