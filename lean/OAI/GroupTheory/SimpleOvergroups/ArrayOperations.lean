import Mathlib
import OAI.GroupTheory.SimpleOvergroups.ArrayNames
import OAI.GroupTheory.SimpleOvergroups.EnlargementCore

namespace OAI

namespace SimpleFInftyOvergroups.EffectiveNames.Array
noncomputable section
open scoped Classical
variable {A G X D V Y : Type*}

def product (cmul : A → A → A) (op : G → X → X) (p : Name A G) (q : Name A X) : Name A X :=
  p.flatMap fun a => q.map fun b => (cmul a.1 b.1,op a.2 b.2)

@[simp] theorem product_nil (cmul : A → A → A) (op : G → X → X) (q : Name A X) :
    product cmul op [] q = [] := rfl
@[simp] theorem product_cons (cmul : A → A → A) (op : G → X → X)
    (a : A × G) (p : Name A G) (q : Name A X) :
    product cmul op (a::p) q = (q.map fun b => (cmul a.1 b.1,op a.2 b.2)) ++ product cmul op p q := rfl

 theorem product_bound (cmul : A → A → A) (op : G → X → X)
    (gc : G → ℕ) (xc : X → ℕ) (hop : ∀ g x, xc (op g x) = gc g + xc x)
    {p : Name A G} {q : Name A X} {b c : ℕ}
    (hp : ∀ a ∈ p, gc a.2 ≤ b) (hq : ∀ a ∈ q, xc a.2 ≤ c) :
    ∀ a ∈ product cmul op p q, xc a.2 ≤ b+c := by
  intro a ha
  obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp ha
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  simpa only [hop] using Nat.add_le_add (hp u hu) (hq w hw)

variable [Ring D] [Group V]
variable (coeff : A → D) (group : G → V)

def algebraValue (p : Name A G) : MonoidAlgebra D V := MonoidAlgebra.ofCoeff (value coeff group p)

@[simp] theorem algebraValue_nil : algebraValue coeff group [] = 0 := rfl
@[simp] theorem algebraValue_cons (a : A × G) (p : Name A G) :
    algebraValue coeff group (a::p) = MonoidAlgebra.single (group a.2) (coeff a.1) + algebraValue coeff group p := rfl
@[simp] theorem algebraValue_append (p q : Name A G) :
    algebraValue coeff group (p++q) = algebraValue coeff group p + algebraValue coeff group q := by
  simp only [algebraValue,value_append,MonoidAlgebra.ofCoeff_add]

 theorem algebraValue_product (cmul : A → A → A) (mul : G → G → G)
    (hc : ∀ a b, coeff (cmul a b) = coeff a * coeff b)
    (hg : ∀ g h, group (mul g h) = group g * group h) (p q : Name A G) :
    algebraValue coeff group (product cmul mul p q) = algebraValue coeff group p * algebraValue coeff group q := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [product_cons,algebraValue_append,ih,algebraValue_cons,add_mul]
    congr 1
    clear ih
    induction q with
    | nil => simp
    | cons b q ih =>
      simp only [List.map_cons,algebraValue_cons,ih,hc,hg,mul_add,MonoidAlgebra.single_mul_single]

variable [MulAction V Y] (point : X → Y)

 theorem value_action (cmul : A → A → A) (act : G → X → X)
    (hc : ∀ a b, coeff (cmul a b) = coeff a * coeff b)
    (ha : ∀ g x, point (act g x) = group g • point x) (p : Name A G) (q : Name A X) :
    value coeff point (product cmul act p q) =
      SourceEnlargement.ringAction (algebraValue coeff group p) (value coeff point q) := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [product_cons,value_append,ih,algebraValue_cons,map_add]
    change _ = SourceEnlargement.ringAction (MonoidAlgebra.single (group a.2) (coeff a.1))
      (value coeff point q) + SourceEnlargement.ringAction (algebraValue coeff group p) (value coeff point q)
    congr 1
    clear ih
    induction q with
    | nil => simp
    | cons b q ih =>
      simp only [List.map_cons,value_cons,ih,hc,ha,map_add,SourceEnlargement.ringAction_single]

variable [Primcodable A] [Primcodable G] [Primcodable X]
 theorem primrec_product {cmul : A → A → A} {op : G → X → X}
    (hc : Primrec₂ cmul) (ho : Primrec₂ op) : Primrec₂ (product cmul op) := by
  unfold product
  apply Primrec.list_flatMap Primrec.fst
  change Primrec (fun p : (Name A G × Name A X) × (A × G) =>
    p.1.2.map fun b => (cmul p.2.1 b.1,op p.2.2 b.2))
  apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
  exact ((hc.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)).pair
    (ho.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))).to₂

end
end SimpleFInftyOvergroups.EffectiveNames.Array

end OAI
